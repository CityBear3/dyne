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
//! - Task 6: `IfExpr` / `Match` / `While` / `For` / `VecLit` / `MatLit` /
//!   `Index` / `Block`-as-expr; introduces `unify::Table` for match-arm
//!   unification. Vec/Mat *operator* shape rules (Vec+Vec, Mat·Vec, etc.)
//!   are still deferred — `synth_arith` returns `Ty::Error` for those.

use std::collections::HashMap;

use crate::ast::{
    BinOp, Block, Expr, ExprKind, ForStmt, FunctionDef, IfExpr, Item, MatchArm, Pattern,
    PatternKind, Program, Stmt, StmtKind, UnaryOp, WhileStmt,
};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{Dimension, Ty, VariantPayload, lower_type};
use crate::sema::unify;
use crate::source::Span;

pub(crate) struct TypeChecker<'a> {
    resolutions: &'a ResolveTable,
    definitions: &'a DefinitionTable,
    pub(crate) def_types: &'a mut HashMap<DefId, Ty>,
    pub(crate) struct_fields: &'a HashMap<DefId, Vec<(String, Ty)>>,
    pub(crate) variant_payloads: &'a HashMap<DefId, VariantPayload>,
    pub(crate) types: HashMap<NodeId, Ty>,
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// Stack-managed by `check_function`: the enclosing function's declared
    /// return type, against which `StmtKind::Return(Some(_))` checks. `None`
    /// at the top level (top-level `Item::Let` init is checked elsewhere).
    current_return_ty: Option<Ty>,
    /// Unification table for match-arm body unification (and PR-3c's enum
    /// constructor inference). Currently only `unify_or_diag` consults it
    /// transitively via `unify::Table::resolve`.
    unify_table: unify::Table,
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
            current_return_ty: None,
            unify_table: unify::Table::new(),
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
            ExprKind::Index(base, idx) => self.synth_index(base, idx),
            ExprKind::VecLit(elems) => self.synth_vec_lit(elems),
            ExprKind::MatLit(rows) => self.synth_mat_lit(e, rows),
            ExprKind::If(if_expr) => self.synth_if(e, if_expr),
            ExprKind::Match(scrut, arms) => self.synth_match(scrut, arms),
            ExprKind::Block(b) => self.synth_block(b),
            // Lambdas remain out of scope for PR-3b (no surface syntax /
            // first-class function values yet).
            ExprKind::Lambda(_) => Ty::Error,
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
        // Resolve through the unification table first so any `Ty::Var`
        // chains collapse to concrete types before we compare. PR-3b only
        // produces concrete types (resolve is a no-op for those); the
        // plumbing is in place for PR-3c's constructor inference.
        let actual = self.unify_table.resolve(actual);
        let expected = self.unify_table.resolve(expected);
        if matches!(actual, Ty::Error) || matches!(expected, Ty::Error) {
            return;
        }
        if actual != expected {
            self.diagnostics.push(crate::sema::diag::type_mismatch_full(
                span, &expected, &actual,
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
            });
        let prev = std::mem::replace(&mut self.current_return_ty, expected_return);
        // Function bodies' "value" is irrelevant — explicit `return`
        // statements check against `current_return_ty`. We discard
        // `synth_block`'s return value here.
        let _ = self.synth_block(&f.body);
        self.current_return_ty = prev;
    }

    /// Walk a block; the block's "value" is the type of its final statement
    /// when that statement is an expression. Everything else (Let, Assign,
    /// Return, For, While) returns `Ty::Error` from `synth_stmt` so the
    /// block's value is `Ty::Error` in those cases — which is fine because
    /// callers that care about block values (if/match arms) only place
    /// expressions in tail position.
    fn synth_block(&mut self, b: &Block) -> Ty {
        let mut last_ty = Ty::Error;
        for stmt in &b.stmts {
            last_ty = self.synth_stmt(stmt);
        }
        last_ty
    }

    fn synth_stmt(&mut self, s: &Stmt) -> Ty {
        match &s.kind {
            StmtKind::Let(l) => {
                // Recover the local let's DefId via (DefKind::LocalLet, name,
                // span). Pass 1 (signature_pass) only handled top-level lets,
                // so the entry may not yet be in def_types; insert it now
                // using the lowered annotation.
                if let Some(def_id) = self.local_let_def_id(&l.name, s.span) {
                    if !self.def_types.contains_key(&def_id) {
                        let lowered = lower_type(
                            &l.ty,
                            self.resolutions,
                            self.definitions,
                            &mut self.diagnostics,
                        );
                        self.def_types.insert(def_id, lowered);
                    }
                    let expected = self.def_types.get(&def_id).cloned().unwrap_or(Ty::Error);
                    self.check_expr(&l.init, &expected);
                } else {
                    // Resolver should have rejected duplicates / unbound
                    // names; just synth so sub-expressions are recorded.
                    self.synth_expr(&l.init);
                }
                Ty::Error
            }
            StmtKind::Assign(_, expr) => {
                let expected = self
                    .resolutions
                    .get(&s.id)
                    .copied()
                    .and_then(|def_id| self.def_types.get(&def_id).cloned())
                    .unwrap_or(Ty::Error);
                self.check_expr(expr, &expected);
                Ty::Error
            }
            StmtKind::Expr(expr) => self.synth_expr(expr),
            StmtKind::Return(Some(expr)) => {
                let expected = self.current_return_ty.clone().unwrap_or(Ty::Error);
                self.check_expr(expr, &expected);
                Ty::Error
            }
            StmtKind::Return(None) => Ty::Error,
            StmtKind::For(for_stmt) => {
                self.synth_for(for_stmt, s.span);
                Ty::Error
            }
            StmtKind::While(w) => {
                self.synth_while(w);
                Ty::Error
            }
        }
    }

    fn local_let_def_id(&self, name: &str, span: Span) -> Option<DefId> {
        self.definitions
            .iter()
            .find(|(_, info)| {
                matches!(info.kind, DefKind::LocalLet) && info.name == name && info.span == span
            })
            .map(|(id, _)| *id)
    }

    fn loop_var_def_id(&self, name: &str, span: Span) -> Option<DefId> {
        self.definitions
            .iter()
            .find(|(_, info)| {
                matches!(info.kind, DefKind::LoopVar) && info.name == name && info.span == span
            })
            .map(|(id, _)| *id)
    }

    fn pattern_binding_def_id(&self, name: &str, span: Span) -> Option<DefId> {
        self.definitions
            .iter()
            .find(|(_, info)| {
                matches!(info.kind, DefKind::PatternBinding)
                    && info.name == name
                    && info.span == span
            })
            .map(|(id, _)| *id)
    }

    fn synth_if(&mut self, e: &Expr, if_expr: &IfExpr) -> Ty {
        self.check_cond(&if_expr.cond);
        let then_ty = self.synth_block(&if_expr.then_block);
        let mut had_arm_mismatch = false;
        for (cond, block) in &if_expr.elseifs {
            self.check_cond(cond);
            let arm_ty = self.synth_block(block);
            let prev = self.diagnostics.len();
            self.unify_or_diag(&arm_ty, &then_ty, e.span);
            if self.diagnostics.len() != prev {
                had_arm_mismatch = true;
            }
        }
        if let Some(else_block) = &if_expr.else_block {
            let arm_ty = self.synth_block(else_block);
            let prev = self.diagnostics.len();
            self.unify_or_diag(&arm_ty, &then_ty, e.span);
            if self.diagnostics.len() != prev {
                had_arm_mismatch = true;
            }
        }
        // No-cascade: when any arm-vs-seed unification already fired a
        // diag, return Ty::Error so the outer context's check_expr
        // doesn't pile a second "type mismatch" on top.
        if had_arm_mismatch { Ty::Error } else { then_ty }
    }

    /// Type-check a condition position. Emits the cond-specific
    /// `non_bool_condition` diagnostic (rather than the generic "type
    /// mismatch") so the message reads naturally for `if`/`while`.
    fn check_cond(&mut self, cond: &Expr) {
        let cond_ty = self.synth_expr(cond);
        if !matches!(cond_ty, Ty::Bool | Ty::Error) {
            self.diagnostics
                .push(crate::sema::diag::non_bool_condition(cond.span, &cond_ty));
        }
    }

    fn synth_match(&mut self, scrutinee: &Expr, arms: &[MatchArm]) -> Ty {
        let scrut_ty = self.synth_expr(scrutinee);
        let Some((first, rest)) = arms.split_first() else {
            return Ty::Error;
        };
        let seed_ty = self.check_match_arm(first, &scrut_ty);
        let mut had_arm_mismatch = false;
        for arm in rest {
            let arm_ty = self.check_match_arm(arm, &scrut_ty);
            let prev = self.diagnostics.len();
            self.unify_or_diag(&arm_ty, &seed_ty, arm.span);
            if self.diagnostics.len() != prev {
                had_arm_mismatch = true;
            }
        }
        // No-cascade: same shape as synth_if. If any arm-vs-seed
        // mismatch already pushed a diag, return Ty::Error so the
        // outer check_expr doesn't fire a second one.
        if had_arm_mismatch { Ty::Error } else { seed_ty }
    }

    fn check_match_arm(&mut self, arm: &MatchArm, scrut_ty: &Ty) -> Ty {
        self.check_pattern(&arm.pattern, scrut_ty);
        self.synth_block(&arm.body)
    }

    fn check_pattern(&mut self, p: &Pattern, expected: &Ty) {
        match &p.kind {
            PatternKind::Wildcard => {}
            PatternKind::IntLit(_) => self.unify_or_diag(&Ty::Int, expected, p.span),
            PatternKind::BoolLit(_) => self.unify_or_diag(&Ty::Bool, expected, p.span),
            PatternKind::StrLit(_) => self.unify_or_diag(&Ty::String, expected, p.span),
            PatternKind::Ident(name) => {
                // The resolver creates a DefKind::PatternBinding for this
                // name (under the pattern's own span). Look it up by
                // (kind, name, span) and record its type as the scrutinee's.
                // Resolutions[p.id] is *not* populated for pattern bindings —
                // that table maps name *uses*, while pattern bindings are
                // introductions.
                if let Some(def_id) = self.pattern_binding_def_id(name, p.span) {
                    self.def_types.insert(def_id, expected.clone());
                }
            }
            PatternKind::Variant(_, sub_patterns) => {
                let Some(variant_def_id) = self.resolutions.get(&p.id).copied() else {
                    return;
                };
                let Some(payload) = self.variant_payloads.get(&variant_def_id).cloned() else {
                    return;
                };
                let parent_matches = matches!(
                    expected,
                    Ty::Enum(scrut_def_id, _) if *scrut_def_id == payload.parent_enum
                );
                if !parent_matches && !matches!(expected, Ty::Error) {
                    self.unify_or_diag(&Ty::Enum(payload.parent_enum, vec![]), expected, p.span);
                    return;
                }
                if sub_patterns.len() != payload.payload.len() {
                    self.diagnostics.push(crate::sema::diag::wrong_arity(
                        p.span,
                        payload.payload.len(),
                        sub_patterns.len(),
                    ));
                    return;
                }
                for (sub, sub_ty) in sub_patterns.iter().zip(payload.payload.iter()) {
                    self.check_pattern(sub, sub_ty);
                }
            }
        }
    }

    fn synth_while(&mut self, w: &WhileStmt) {
        self.check_cond(&w.cond);
        self.synth_block(&w.body);
    }

    fn synth_for(&mut self, f: &ForStmt, outer_span: Span) {
        match f {
            ForStmt::Range {
                var,
                start,
                end,
                body,
            } => {
                self.check_expr(start, &Ty::Int);
                self.check_expr(end, &Ty::Int);
                if let Some(loop_def_id) = self.loop_var_def_id(var, outer_span) {
                    self.def_types.insert(loop_def_id, Ty::Int);
                }
                self.synth_block(body);
            }
            ForStmt::Iter { var, iter, body } => {
                let iter_ty = self.synth_expr(iter);
                let elem_ty = match &iter_ty {
                    Ty::Array(t) => (**t).clone(),
                    Ty::Vec(_, dim) => Ty::Scalar(*dim),
                    Ty::Error => Ty::Error,
                    other => {
                        self.diagnostics.push(crate::sema::diag::op_type_error(
                            iter.span,
                            "for-in iteration",
                            other,
                        ));
                        Ty::Error
                    }
                };
                if let Some(loop_def_id) = self.loop_var_def_id(var, outer_span) {
                    self.def_types.insert(loop_def_id, elem_ty);
                }
                self.synth_block(body);
            }
            ForStmt::IterKV {
                key,
                value,
                iter,
                body,
            } => {
                let iter_ty = self.synth_expr(iter);
                let (k_ty, v_ty) = match &iter_ty {
                    Ty::Dict(k, v) => ((**k).clone(), (**v).clone()),
                    Ty::Error => (Ty::Error, Ty::Error),
                    other => {
                        self.diagnostics.push(crate::sema::diag::op_type_error(
                            iter.span,
                            "for-key-value iteration",
                            other,
                        ));
                        (Ty::Error, Ty::Error)
                    }
                };
                if let Some(k_def_id) = self.loop_var_def_id(key, outer_span) {
                    self.def_types.insert(k_def_id, k_ty);
                }
                if let Some(v_def_id) = self.loop_var_def_id(value, outer_span) {
                    self.def_types.insert(v_def_id, v_ty);
                }
                self.synth_block(body);
            }
        }
    }

    fn synth_vec_lit(&mut self, elems: &[Expr]) -> Ty {
        // Empty vec literals aren't currently parseable; defensive return.
        let Some((first, rest)) = elems.split_first() else {
            return Ty::Error;
        };
        let first_ty = self.synth_expr(first);
        // Subsequent elements check against the first; using `check_expr`
        // (rather than synth + unify_or_diag) lets the IntLit→Scalar(ZERO)
        // gate widen int literals when the seed is a dimensionless Scalar.
        for el in rest {
            self.check_expr(el, &first_ty);
        }
        let dim = match &first_ty {
            Ty::Scalar(d) => *d,
            // Int / Error / anything else: treat as dimensionless. PR-3d
            // refines unit propagation through literals.
            _ => Dimension::ZERO,
        };
        Ty::Vec(elems.len(), dim)
    }

    fn synth_mat_lit(&mut self, e: &Expr, rows: &[Vec<Expr>]) -> Ty {
        let Some(first_row) = rows.first() else {
            return Ty::Error;
        };
        let cols = first_row.len();
        if cols == 0 {
            return Ty::Error;
        }
        for row in rows {
            if row.len() != cols {
                self.diagnostics.push(crate::sema::diag::mat_shape_mismatch(
                    e.span,
                    (rows.len(), cols),
                    (rows.len(), row.len()),
                ));
                // Bail on shape mismatch to keep the no-cascade invariant.
                return Ty::Error;
            }
            for cell in row {
                let cell_ty = self.synth_expr(cell);
                if !matches!(cell_ty, Ty::Int | Ty::Scalar(_) | Ty::Error) {
                    self.diagnostics.push(crate::sema::diag::op_type_error(
                        cell.span,
                        "matrix cell",
                        &cell_ty,
                    ));
                }
            }
        }
        Ty::Mat(rows.len(), cols)
    }

    fn synth_index(&mut self, base: &Expr, idx: &Expr) -> Ty {
        let base_ty = self.synth_expr(base);
        // Route the index through `check_expr` so the IntLit→Scalar(ZERO)
        // implicit-conversion gate (DD line 143) fires when, e.g., a
        // `Dict<Scalar, _>` is indexed with an int literal.
        match base_ty {
            Ty::Array(t) => {
                self.check_expr(idx, &Ty::Int);
                *t
            }
            Ty::Vec(_, dim) => {
                self.check_expr(idx, &Ty::Int);
                Ty::Scalar(dim)
            }
            Ty::Dict(k, v) => {
                self.check_expr(idx, &k);
                *v
            }
            Ty::Error => {
                // Still record the index expression's type for downstream
                // tooling / future analyses.
                self.synth_expr(idx);
                Ty::Error
            }
            other => {
                self.synth_expr(idx);
                self.diagnostics.push(crate::sema::diag::op_type_error(
                    base.span, "indexing", &other,
                ));
                Ty::Error
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

    // ----- PR-3b Task 6: control flow / collections / index / unify -----

    #[test]
    fn if_cond_must_be_bool() {
        // `if 1 then ... end`: cond is Int, expected Bool. Exactly 1 diag.
        let diags = diags_for(
            "function f(): Int\n  if 1 then\n    return 0\n  else\n    return 1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Bool"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn if_arms_must_unify() {
        // Then arm produces Int, else arm produces Bool: arms must unify.
        let diags = diags_for(
            "function f(): Int\n  if 1 < 2 then\n    1\n  else\n    true\n  end\n  return 0\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("type mismatch"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_arm_bodies_must_unify() {
        let diags = diags_for(
            "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(m: Maybe): Int\n  return match m\n    case Just(x) then x\n    case Nothing then true\n  end\nend",
        );
        // First arm seeds Int; second arm produces Bool → 1 unification diag.
        // (The function-return unify against Int absorbs the Ty::Error from
        // the failing match without an additional diag.)
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("type mismatch"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn while_cond_must_be_bool() {
        let diags =
            diags_for("function f(): Int\n  while 1 do\n    return 0\n  end\n  return 1\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Bool"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn for_range_start_must_be_int() {
        let diags = diags_for(
            "function f(): Int\n  for i = true, 5 do\n    return i\n  end\n  return 0\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Int"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn vec_lit_uniform_succeeds() {
        compile_src("let v: Vec<3> = [1.0, 2.0, 3.0]");
    }

    #[test]
    fn vec_lit_element_mismatch_diag() {
        let diags = diags_for("let v: Vec<3> = [1.0, true, 3.0]");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("type mismatch"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn mat_lit_non_rectangular_diag() {
        let diags = diags_for("let m: Mat<2, 3> = [[1.0, 2.0, 3.0], [4.0, 5.0]]");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("shape") || diags[0].message.contains("rows"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn index_array_returns_element_type() {
        // `xs[0]` returns Int; the function's Bool return forces a mismatch.
        let diags = diags_for("function f(xs: Array<Int>): Bool\n  return xs[0]\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("type mismatch"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn index_dict_returns_value_type() {
        // `d[0]` returns String; function returns Int → mismatch.
        let diags = diags_for("function f(d: Dict<Int, String>): Int\n  return d[0]\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("type mismatch"),
            "msg: {}",
            diags[0].message
        );
    }

    // ----- Regression tests for code-quality fixes (Task 6 follow-up) -----

    #[test]
    fn if_arm_mismatch_does_not_cascade_to_outer() {
        // Then arm = Int, else arm = Bool: 1 unification diag from synth_if.
        // Pre-fix, synth_if returned then_ty (Int), so check_expr against the
        // function's `String` return then fired a *second* diag.
        let diags = diags_for("function f(): String\n  return if 1 < 2 then 1 else true end\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Bool"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_arm_mismatch_does_not_cascade_to_outer() {
        // First arm body = Bool; second arm body = Int. Function returns Int.
        // Pre-fix, synth_match returned seed_ty (Bool), so check_expr against
        // Int fired a second diag.
        let diags = diags_for(
            "function f(): Int\n  return match 1\n    case 1 then true\n    case _ then 2\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
    }

    #[test]
    fn dict_index_with_int_literal_widens_to_scalar_key() {
        // `Dict<Scalar, Int>` indexed with `5` (IntLit) — the
        // IntLit→Scalar(ZERO) coercion should fire because synth_index
        // routes through check_expr.
        compile_src("function f(d: Dict<Scalar, Int>): Int\n  return d[5]\nend");
    }

    #[test]
    fn vec_lit_widens_int_lit_to_scalar() {
        // `[1.0, 2, 3.0]` — first element is FloatLit (Scalar(ZERO));
        // subsequent IntLit element should widen via check_expr's
        // IntLit→Scalar(ZERO) gate, not error out.
        compile_src("function f(): Vec<3>\n  return [1.0, 2, 3.0]\nend");
    }
}
