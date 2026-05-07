//! Bidirectional type checker (Pass 2).
//!
//! Run after `sema::signature_pass`. Walks every function body and top-level
//! let init expression, populating the `TypeTable` and emitting diagnostics
//! for type errors.
//!
//! Task 4 lands the synth/check skeleton and the simplest type rules:
//! literals, identifiers, primitive operators (arithmetic / comparison /
//! logical / unary). Other expression kinds (Call, FieldAccess, VecLit,
//! MatLit, IfExpr, Match, Lambda, StructLit, Index, Block-as-expr) record
//! `Ty::Error` and are filled in by Tasks 5–6.

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
    #[allow(dead_code)] // Consumed in Task 5 (struct literals / field access).
    pub(crate) struct_fields: &'a HashMap<DefId, Vec<(String, Ty)>>,
    #[allow(dead_code)] // Consumed in Task 5–6 (variant constructors / patterns).
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
            // Tasks 5–6 land these. Recording `Ty::Error` here without a
            // diagnostic prevents cascading errors.
            ExprKind::Call(_, _)
            | ExprKind::Index(_, _)
            | ExprKind::FieldAccess(_, _)
            | ExprKind::VecLit(_)
            | ExprKind::MatLit(_)
            | ExprKind::Lambda(_)
            | ExprKind::StructLit(_, _)
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
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                self.synth_arith(&lt, &rt, l.span, r.span)
            }
            BinOp::Pow => self.synth_pow(&lt, &rt, l.span, r.span),
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.synth_comparison(&lt, &rt, l.span)
            }
            BinOp::And | BinOp::Or => self.synth_logical(&lt, &rt, l.span),
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

    /// Arithmetic on `Int` / `Scalar`. Vec/Mat arithmetic is valid dyne but
    /// lands in Task 6; here it returns `Ty::Error` without a diagnostic so
    /// the no-cascade invariant holds.
    fn synth_arith(&mut self, l: &Ty, r: &Ty, l_span: Span, r_span: Span) -> Ty {
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
                    r_span,
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
                l_span,
                "comparison operands must have the same primitive type",
            ));
            Ty::Error
        }
    }

    fn synth_logical(&mut self, l: &Ty, r: &Ty, l_span: Span) -> Ty {
        if matches!(l, Ty::Bool) && matches!(r, Ty::Bool) {
            Ty::Bool
        } else {
            self.diagnostics.push(crate::sema::diag::op_type_error(
                l_span,
                "logical (`&&` / `||`)",
                l,
            ));
            Ty::Error
        }
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
        assert!(
            diags.iter().any(|d| d.message.contains("arithmetic")),
            "diags: {:?}",
            diags
        );
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
        assert!(
            diags.iter().any(|d| d.message.contains("logical")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn unary_neg_on_bool_diag() {
        let diags = diags_for("function f(): Int\n  return -true\nend");
        assert!(
            diags.iter().any(|d| d.message.contains("unary")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn unary_not_on_int_diag() {
        let diags = diags_for("function f(): Bool\n  return not 5\nend");
        assert!(
            diags.iter().any(|d| d.message.contains("not")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn ident_resolves_to_param_type() {
        compile_src("function f(x: Int): Int\n  return x\nend");
    }

    #[test]
    fn return_value_type_mismatch_diag() {
        let diags = diags_for("function f(): Int\n  return true\nend");
        assert!(
            diags.iter().any(|d| d.message.contains("type mismatch")),
            "diags: {:?}",
            diags
        );
    }
}
