//! Bidirectional type checker (Pass 2).
//!
//! Run after `sema::signature_pass`. Walks every function body and top-level
//! let init expression, populating the `TypeTable` and emitting diagnostics
//! for type errors.
//!
//! - Task 4: synth/check skeleton + literal / identifier / arithmetic /
//!   comparison / logical / unary rules + `Int → Scalar(ZERO)` implicit
//!   conversion in checking mode.
//! - Task 5: `Call` (arity + arg-type), `StructLit` (per-field check vs
//!   declaration; missing/extra diagnostics), `FieldAccess` (struct →
//!   field Ty lookup).
//! - Task 6 (pending): `IfExpr` / `Match` / `While` / `For` / `VecLit` /
//!   `MatLit` / `Index` / `Block`-as-expr / Vec-Mat operator shape rules.
//!   These currently record `Ty::Error` without diagnostics.

use std::collections::HashMap;

use crate::ast::{
    BinOp, Expr, ExprKind, ForStmt, FunctionDef, Item, Program, Stmt, StmtKind, UnaryOp,
};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{Dimension, Ty, VariantPayload};
use crate::source::Span;

pub(crate) struct TypeChecker<'a> {
    resolutions: &'a ResolveTable,
    definitions: &'a DefinitionTable,
    pub(crate) def_types: &'a mut HashMap<DefId, Ty>,
    pub(crate) struct_fields: &'a HashMap<DefId, Vec<(String, Ty)>>,
    #[allow(dead_code)] // Consumed in Task 6 (variant constructors / patterns).
    pub(crate) variant_payloads: &'a HashMap<DefId, VariantPayload>,
    pub(crate) types: HashMap<NodeId, Ty>,
    pub(crate) diagnostics: Vec<Diagnostic>,
    // unify::Table goes here in Task 6.
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn new(
        resolutions: &'a ResolveTable,
        definitions: &'a DefinitionTable,
        def_types: &'a mut HashMap<DefId, Ty>,
        struct_fields: &'a HashMap<DefId, Vec<(String, Ty)>>,
        variant_payloads: &'a HashMap<DefId, VariantPayload>,
    ) -> Self {
        Self {
            resolutions,
            definitions,
            def_types,
            struct_fields,
            variant_payloads,
            types: HashMap::new(),
            diagnostics: Vec::new(),
        }
    }

    fn record(&mut self, id: NodeId, ty: Ty) -> Ty {
        self.types.insert(id, ty.clone());
        ty
    }

    /// Synthesize an expression's type. Records the result in `types` and
    /// returns it.
    fn synth_expr(&mut self, e: &Expr) -> Ty {
        let ty = match &e.kind {
            ExprKind::IntLit(_) => Ty::Int,
            ExprKind::FloatLit(_) => Ty::Scalar(Dimension::ZERO),
            ExprKind::BoolLit(_) => Ty::Bool,
            ExprKind::StrLit(_) => Ty::String,
            ExprKind::Ident(_) => self.synth_ident(e),
            ExprKind::BinOp(op, l, r) => self.synth_binop(*op, l, r),
            ExprKind::UnaryOp(op, x) => self.synth_unaryop(*op, x),
            ExprKind::Call(callee, args) => self.synth_call(callee, args, e.span),
            ExprKind::StructLit(name, fields) => self.synth_struct_lit(e, name, fields),
            ExprKind::FieldAccess(base, field) => self.synth_field_access(base, field),
            // Task 6 lands these. Recording `Ty::Error` here without a
            // diagnostic prevents cascading errors.
            ExprKind::Index(_, _)
            | ExprKind::VecLit(_)
            | ExprKind::MatLit(_)
            | ExprKind::Lambda(_)
            | ExprKind::If(_)
            | ExprKind::Match(_, _)
            | ExprKind::Block(_) => Ty::Error,
        };
        self.record(e.id, ty)
    }

    /// Check an expression against an expected type. Records the type and
    /// emits a diagnostic on mismatch.
    fn check_expr(&mut self, e: &Expr, expected: &Ty) -> Ty {
        // Implicit Int → dimensionless Scalar conversion (DD line 143). Only
        // applies in checking mode and only when the expected dimension is
        // `ZERO`. Synthesis never widens an Int.
        if let (ExprKind::IntLit(_), Ty::Scalar(d)) = (&e.kind, expected)
            && d.is_dimensionless()
        {
            let ty = Ty::Scalar(Dimension::ZERO);
            return self.record(e.id, ty);
        }
        let synthesized = self.synth_expr(e);
        self.unify_or_diag(&synthesized, expected, e.span);
        synthesized
    }

    fn synth_ident(&mut self, e: &Expr) -> Ty {
        let Some(def_id) = self.resolutions.get(&e.id).copied() else {
            return Ty::Error; // resolver already reported
        };
        self.def_types.get(&def_id).cloned().unwrap_or(Ty::Error)
    }

    fn synth_binop(&mut self, op: BinOp, l: &Expr, r: &Expr) -> Ty {
        let lt = self.synth_expr(l);
        let rt = self.synth_expr(r);
        if matches!(lt, Ty::Error) || matches!(rt, Ty::Error) {
            return Ty::Error;
        }
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => self.synth_arith(&lt, &rt, l.span),
            BinOp::Pow => self.synth_pow(&lt, &rt, l.span, r.span),
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.synth_comparison(&lt, &rt, l.span)
            }
            BinOp::And | BinOp::Or => self.synth_logical(&lt, &rt, l.span, r.span),
        }
    }

    fn synth_unaryop(&mut self, op: UnaryOp, x: &Expr) -> Ty {
        let xt = self.synth_expr(x);
        if matches!(xt, Ty::Error) {
            return Ty::Error;
        }
        match op {
            UnaryOp::Neg => match &xt {
                Ty::Int => Ty::Int,
                Ty::Scalar(d) => Ty::Scalar(*d),
                // Vec/Mat negation is valid dyne; Task 6 lands the rule.
                // Suppress the diagnostic here so the no-cascade invariant
                // holds.
                Ty::Vec(_, _) | Ty::Mat(_, _) => Ty::Error,
                _ => {
                    self.diagnostics.push(crate::sema::diag::op_type_error(
                        x.span,
                        "unary `-`",
                        &xt,
                    ));
                    Ty::Error
                }
            },
            UnaryOp::Not => {
                if matches!(xt, Ty::Bool) {
                    Ty::Bool
                } else {
                    self.diagnostics.push(crate::sema::diag::op_type_error(
                        x.span,
                        "unary `not`",
                        &xt,
                    ));
                    Ty::Error
                }
            }
        }
    }

    /// Function call: synth callee, expect `Ty::Function(param_tys, ret)`,
    /// check each argument against its declared param type, return `ret`.
    /// Non-function callees emit `not_callable`; arity mismatches emit
    /// `wrong_arity`. In both error cases we skip per-argument checking so
    /// downstream diagnostics don't cascade.
    fn synth_call(&mut self, callee: &Expr, args: &[Expr], call_span: Span) -> Ty {
        let callee_ty = self.synth_expr(callee);
        match callee_ty {
            Ty::Error => Ty::Error,
            Ty::Function(param_tys, ret_ty) => {
                if param_tys.len() != args.len() {
                    self.diagnostics.push(crate::sema::diag::wrong_arity(
                        call_span,
                        param_tys.len(),
                        args.len(),
                    ));
                    // Return Ty::Error so the call's surrounding context
                    // (e.g. `unify_or_diag` against the function's declared
                    // return type) doesn't cascade into a second diag. Per
                    // the no-cascade watchpoint: a structural error already
                    // pinned by `wrong_arity` shouldn't also produce a
                    // "expected T, found U" mismatch downstream.
                    return Ty::Error;
                }
                for (arg, expected) in args.iter().zip(param_tys.iter()) {
                    self.check_expr(arg, expected);
                }
                *ret_ty
            }
            other => {
                self.diagnostics
                    .push(crate::sema::diag::not_callable(callee.span, &other));
                Ty::Error
            }
        }
    }

    /// Struct literal: resolver records the struct's `DefId` against the
    /// `StructLit` expression's NodeId. Each provided field is checked
    /// against the struct's declared field type; missing/extra fields
    /// each produce their own diagnostic.
    fn synth_struct_lit(&mut self, e: &Expr, name: &str, fields: &[(String, Expr)]) -> Ty {
        let Some(def_id) = self.resolutions.get(&e.id).copied() else {
            // Resolver already reported the unknown struct name.
            for (_, fexpr) in fields {
                self.synth_expr(fexpr);
            }
            return Ty::Error;
        };
        let Some(declared_fields) = self.struct_fields.get(&def_id).cloned() else {
            // The name resolved to something that isn't a struct (e.g. an
            // enum constructor). Resolver may not have flagged this; just
            // record `Ty::Error`. PR-3c may refine this with a clearer diag.
            for (_, fexpr) in fields {
                self.synth_expr(fexpr);
            }
            return Ty::Error;
        };

        let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for (fname, fexpr) in fields {
            seen.insert(fname.as_str());
            match declared_fields
                .iter()
                .find(|(declared, _)| declared == fname)
            {
                Some((_, declared_ty)) => {
                    self.check_expr(fexpr, declared_ty);
                }
                None => {
                    self.diagnostics
                        .push(crate::sema::diag::extra_struct_field(e.span, name, fname));
                    // Still record the expression's type for later passes.
                    self.synth_expr(fexpr);
                }
            }
        }
        for (declared_name, _) in &declared_fields {
            if !seen.contains(declared_name.as_str()) {
                self.diagnostics
                    .push(crate::sema::diag::missing_struct_field(
                        e.span,
                        name,
                        declared_name,
                    ));
            }
        }
        Ty::Struct(def_id)
    }

    /// Field access: base must synthesize to `Ty::Struct(def_id)`. The
    /// field name is looked up in `struct_fields[def_id]`. Unknown field
    /// emits `field_unknown`; non-struct base emits a generic
    /// `op_type_error` on field-access.
    fn synth_field_access(&mut self, base: &Expr, field: &str) -> Ty {
        let base_ty = self.synth_expr(base);
        match &base_ty {
            Ty::Error => Ty::Error,
            Ty::Struct(def_id) => {
                let struct_name = self
                    .definitions
                    .get(def_id)
                    .map(|info| info.name.as_str())
                    .unwrap_or("<struct>");
                let Some(declared_fields) = self.struct_fields.get(def_id) else {
                    return Ty::Error;
                };
                match declared_fields.iter().find(|(name, _)| name == field) {
                    Some((_, ty)) => ty.clone(),
                    None => {
                        self.diagnostics.push(crate::sema::diag::field_unknown(
                            base.span,
                            struct_name,
                            field,
                        ));
                        Ty::Error
                    }
                }
            }
            _ => {
                self.diagnostics.push(crate::sema::diag::op_type_error(
                    base.span,
                    "field access",
                    &base_ty,
                ));
                Ty::Error
            }
        }
    }

    /// Arithmetic on `Int` / `Scalar`. Vec/Mat arithmetic is valid dyne but
    /// lands in Task 6; here it returns `Ty::Error` without a diagnostic so
    /// the no-cascade invariant holds.
    fn synth_arith(&mut self, l: &Ty, r: &Ty, l_span: Span) -> Ty {
        match (l, r) {
            (Ty::Int, Ty::Int) => Ty::Int,
            (Ty::Int, Ty::Scalar(d)) | (Ty::Scalar(d), Ty::Int) if d.is_dimensionless() => {
                Ty::Scalar(Dimension::ZERO)
            }
            (Ty::Scalar(_), Ty::Scalar(_)) => Ty::Scalar(Dimension::ZERO),
            // Defer to Task 6 silently.
            (Ty::Vec(_, _) | Ty::Mat(_, _), _) | (_, Ty::Vec(_, _) | Ty::Mat(_, _)) => Ty::Error,
            _ => {
                self.diagnostics.push(crate::sema::diag::type_mismatch(
                    l_span,
                    "arithmetic operands must both be Int or Scalar",
                ));
                Ty::Error
            }
        }
    }

    /// Pow: base must be `Int` or `Scalar`; exponent must be `Int`.
    fn synth_pow(&mut self, l: &Ty, r: &Ty, l_span: Span, r_span: Span) -> Ty {
        let result = match l {
            Ty::Int => Ty::Int,
            Ty::Scalar(d) => Ty::Scalar(*d),
            // Vec/Mat power is not yet decided; defer silently.
            Ty::Vec(_, _) | Ty::Mat(_, _) => return Ty::Error,
            _ => Ty::Error,
        };
        if !matches!(r, Ty::Int) {
            self.diagnostics
                .push(crate::sema::diag::op_type_error(r_span, "`**` exponent", r));
        }
        if matches!(result, Ty::Error) {
            self.diagnostics
                .push(crate::sema::diag::op_type_error(l_span, "`**` base", l));
        }
        result
    }

    fn synth_comparison(&mut self, l: &Ty, r: &Ty, l_span: Span) -> Ty {
        let same_primitive = l == r && matches!(l, Ty::Int | Ty::Scalar(_) | Ty::Bool | Ty::String);
        let int_scalar_pair = matches!(
            (l, r),
            (Ty::Int, Ty::Scalar(d)) | (Ty::Scalar(d), Ty::Int) if d.is_dimensionless()
        );
        if same_primitive || int_scalar_pair {
            Ty::Bool
        } else {
            self.diagnostics.push(crate::sema::diag::type_mismatch(
                l_span,
                "comparison operands must have the same primitive type",
            ));
            Ty::Error
        }
    }

    fn synth_logical(&mut self, l: &Ty, r: &Ty, l_span: Span, r_span: Span) -> Ty {
        if matches!(l, Ty::Bool) && matches!(r, Ty::Bool) {
            return Ty::Bool;
        }
        // Point the diagnostic at the actual non-Bool operand rather than
        // unconditionally at `l`. When both sides are non-Bool we pick the
        // left; that's a reasonable default and the message names the
        // offending type.
        let (offender, span) = if !matches!(l, Ty::Bool) {
            (l, l_span)
        } else {
            (r, r_span)
        };
        self.diagnostics.push(crate::sema::diag::op_type_error(
            span,
            "logical (`&&` / `||`)",
            offender,
        ));
        Ty::Error
    }

    fn unify_or_diag(&mut self, actual: &Ty, expected: &Ty, span: Span) {
        if matches!(actual, Ty::Error) || matches!(expected, Ty::Error) {
            return;
        }
        if actual != expected {
            self.diagnostics.push(crate::sema::diag::type_mismatch_full(
                span, expected, actual,
            ));
        }
    }

    fn check_function(&mut self, f: &FunctionDef) {
        let expected_return = self
            .definitions
            .iter()
            .find(|(_, info)| matches!(info.kind, DefKind::Function) && info.name == f.name)
            .and_then(|(id, _)| self.def_types.get(id))
            .and_then(|sig| match sig {
                Ty::Function(_, ret) => Some((**ret).clone()),
                _ => None,
            })
            .unwrap_or(Ty::Error);
        for stmt in &f.body.stmts {
            self.check_stmt(stmt, &expected_return);
        }
    }

    fn check_stmt(&mut self, s: &Stmt, expected_return: &Ty) {
        match &s.kind {
            // Local `let` typing lands in Tasks 5–6 (it needs the unify table
            // for inference of un-annotated init forms). For now, just walk
            // the init so its sub-expressions are recorded in `types`.
            StmtKind::Let(l) => {
                self.synth_expr(&l.init);
            }
            StmtKind::Assign(_, expr) => {
                self.synth_expr(expr);
            }
            StmtKind::Expr(expr) => {
                self.synth_expr(expr);
            }
            StmtKind::Return(Some(expr)) => {
                self.check_expr(expr, expected_return);
            }
            StmtKind::Return(None) => {}
            StmtKind::For(for_stmt) => match for_stmt {
                ForStmt::Range {
                    start, end, body, ..
                } => {
                    self.synth_expr(start);
                    self.synth_expr(end);
                    for stmt in &body.stmts {
                        self.check_stmt(stmt, expected_return);
                    }
                }
                ForStmt::Iter { iter, body, .. } => {
                    self.synth_expr(iter);
                    for stmt in &body.stmts {
                        self.check_stmt(stmt, expected_return);
                    }
                }
                ForStmt::IterKV { iter, body, .. } => {
                    self.synth_expr(iter);
                    for stmt in &body.stmts {
                        self.check_stmt(stmt, expected_return);
                    }
                }
            },
            StmtKind::While(w) => {
                self.synth_expr(&w.cond);
                for stmt in &w.body.stmts {
                    self.check_stmt(stmt, expected_return);
                }
            }
        }
    }
}

pub(crate) fn run(
    program: &Program,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    def_types: &mut HashMap<DefId, Ty>,
    struct_fields: &HashMap<DefId, Vec<(String, Ty)>>,
    variant_payloads: &HashMap<DefId, VariantPayload>,
) -> (HashMap<NodeId, Ty>, Vec<Diagnostic>) {
    let mut tc = TypeChecker::new(
        resolutions,
        definitions,
        def_types,
        struct_fields,
        variant_payloads,
    );

    // Reverse-name index over hoisted top-level definitions (matches the
    // shape `signature_pass` uses). Lets `Item::Let` recover its DefId.
    let name_to_def: HashMap<&str, DefId> = tc
        .definitions
        .iter()
        .filter(|(_, info)| matches!(info.kind, DefKind::TopLevelLet))
        .map(|(id, info)| (info.name.as_str(), *id))
        .collect();

    for item in &program.items {
        match item {
            Item::Function(f) => tc.check_function(f),
            Item::Let(l) => {
                let expected = name_to_def
                    .get(l.name.as_str())
                    .copied()
                    .and_then(|id| tc.def_types.get(&id).cloned())
                    .unwrap_or(Ty::Error);
                tc.check_expr(&l.init, &expected);
            }
            Item::Struct(_) | Item::Enum(_) | Item::Import(_) => {}
        }
    }
    (tc.types, tc.diagnostics)
}

#[cfg(test)]
mod tests {
    use crate::lexer::tokenize;
    use crate::parser::parse;
    use crate::sema::check;

    fn compile_src(src: &str) {
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let _typed = check(prog).expect("ok");
    }

    fn diags_for(src: &str) -> Vec<crate::diag::Diagnostic> {
        let prog = parse(tokenize(src).unwrap()).unwrap();
        check(prog).expect_err("expected diags")
    }

    #[test]
    fn synth_int_literal_in_function_body_succeeds() {
        compile_src("function f(): Int\n  return 42\nend");
    }

    #[test]
    fn synth_addition_int_int_returns_int() {
        compile_src("function f(): Int\n  return 1 + 2\nend");
    }

    #[test]
    fn synth_addition_int_string_diag() {
        let diags = diags_for("function f(): Int\n  return 1 + \"x\"\nend");
        // No-cascade: the arithmetic mismatch is the only diagnostic;
        // unify_or_diag silently returns when the synthesized type is
        // already `Ty::Error`.
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("arithmetic"));
    }

    #[test]
    fn check_int_literal_against_scalar_zero_succeeds() {
        compile_src("let x: Scalar = 5");
    }

    #[test]
    fn comparison_returns_bool() {
        compile_src("function f(): Bool\n  return 1 < 2\nend");
    }

    #[test]
    fn logical_and_requires_both_bool() {
        let diags = diags_for("function f(): Bool\n  return true and 1\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("logical"));
    }

    #[test]
    fn unary_neg_on_bool_diag() {
        let diags = diags_for("function f(): Int\n  return -true\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("unary"));
    }

    #[test]
    fn unary_not_on_int_diag() {
        let diags = diags_for("function f(): Bool\n  return not 5\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("not"));
    }

    #[test]
    fn ident_resolves_to_param_type() {
        compile_src("function f(x: Int): Int\n  return x\nend");
    }

    #[test]
    fn return_value_type_mismatch_diag() {
        let diags = diags_for("function f(): Int\n  return true\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("type mismatch"));
    }

    // ----- Coverage gaps surfaced by code-quality review -----

    #[test]
    fn logical_and_diag_names_the_non_bool_operand() {
        // Regression for the `synth_logical` offender bug: when only the
        // right side is non-Bool, the diagnostic must name the non-Bool
        // type (`Int`), not the valid-Bool left side.
        let diags = diags_for("function f(): Bool\n  return true and 1\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("`Int`"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn pow_int_int_returns_int() {
        // Pow base = Int, exponent = Int → Int. Function expects Int return,
        // so unify succeeds.
        compile_src("function f(): Int\n  return 2 ^ 3\nend");
    }

    #[test]
    fn pow_bool_base_emits_diag() {
        // Pow rejects Bool base; the message names the offending side.
        let diags = diags_for("function f(): Int\n  return true ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("base"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn ident_resolves_to_top_level_let() {
        // Top-level `let pi: Scalar = 3.14` populates `def_types[pi]` in
        // signature_pass; reading `pi` from inside a function body must
        // produce `Ty::Scalar(ZERO)` (matching the function's declared
        // return type).
        compile_src("let pi: Scalar = 3.14\nfunction f(): Scalar\n  return pi\nend");
    }

    #[test]
    fn no_cascade_in_chained_arithmetic() {
        // `1 + "x" + 2` parses as `(1 + "x") + 2`. The inner BinOp emits
        // exactly one diag; the outer BinOp's early-exit on Ty::Error
        // suppresses a second one.
        let diags = diags_for("function f(): Int\n  return 1 + \"x\" + 2\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("arithmetic"));
    }

    // ----- PR-3b Task 5: call / struct literal / field access -----

    #[test]
    fn call_with_correct_args_succeeds() {
        compile_src(
            "function add(a: Int, b: Int): Int\n  return a + b\nend\nfunction g(): Int\n  return add(1, 2)\nend",
        );
    }

    #[test]
    fn call_with_wrong_arity_diag() {
        let diags = diags_for(
            "function add(a: Int, b: Int): Int\n  return a + b\nend\nfunction g(): Int\n  return add(1)\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("expected 2, found 1"));
    }

    #[test]
    fn arity_mismatch_does_not_cascade_to_return_check() {
        // Regression for the cascade bug: previously synth_call's
        // arity-mismatch arm returned `*ret_ty`, causing unify_or_diag to
        // fire a second "type mismatch" diag whenever the call appeared in
        // a context expecting a different return type. Now the arm returns
        // Ty::Error, which the no-cascade rule absorbs.
        let diags = diags_for(
            "function add(a: Int, b: Int): Int\n  return a + b\nend\nfunction g(): String\n  return add(1)\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("expected 2, found 1"));
    }

    #[test]
    fn call_with_wrong_arg_type_diag() {
        let diags = diags_for(
            "function add(a: Int, b: Int): Int\n  return a + b\nend\nfunction g(): Int\n  return add(true, 2)\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("type mismatch"));
    }

    #[test]
    fn call_non_function_diag() {
        let diags = diags_for("let x: Int = 5\nfunction f(): Int\n  return x(1)\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("not callable"));
    }

    #[test]
    fn struct_literal_with_correct_fields_succeeds() {
        compile_src(
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Point { x: 1.0, y: 2.0 }",
        );
    }

    #[test]
    fn struct_literal_missing_field_diag() {
        let diags = diags_for(
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Point { x: 1.0 }",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("missing field `y`"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn struct_literal_extra_field_diag() {
        let diags =
            diags_for("struct Point\n  x: Scalar\nend\nlet p: Point = Point { x: 1.0, y: 2.0 }");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("`y`"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn field_access_succeeds() {
        compile_src(
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nfunction f(p: Point): Scalar\n  return p.x\nend",
        );
    }

    #[test]
    fn field_access_unknown_field_diag() {
        let diags = diags_for(
            "struct Point\n  x: Scalar\nend\nfunction f(p: Point): Scalar\n  return p.zzz\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("`zzz`"),
            "msg: {}",
            diags[0].message
        );
    }
}
