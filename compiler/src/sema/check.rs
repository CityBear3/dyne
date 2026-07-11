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
//!   return an approximate Vec/Mat result so cross-context unification
//!   produces accurate diagnostics; PR-3d (Option β: silent ZERO-strip)
//!   activates real unit propagation through these operators.

use std::collections::HashMap;

use crate::ast::{
    Block, Expr, ExprKind, ForStmt, FunctionDef, IfExpr, Item, Program, Stmt, StmtKind, UnaryOp,
    WhileStmt,
};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::dimension::Dimension;
use crate::sema::resolve::{BindingTable, DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{Ty, VariantPayload, lower_type};
use crate::sema::unify;
use crate::source::Span;

mod calls;
mod operators;
mod patterns;

pub(crate) struct TypeChecker<'a> {
    resolutions: &'a ResolveTable,
    definitions: &'a DefinitionTable,
    binding_def_ids: &'a BindingTable,
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
        binding_def_ids: &'a BindingTable,
        def_types: &'a mut HashMap<DefId, Ty>,
        struct_fields: &'a HashMap<DefId, Vec<(String, Ty)>>,
        variant_payloads: &'a HashMap<DefId, VariantPayload>,
    ) -> Self {
        Self {
            resolutions,
            definitions,
            binding_def_ids,
            def_types,
            struct_fields,
            variant_payloads,
            types: HashMap::new(),
            diagnostics: Vec::new(),
            current_return_ty: None,
            unify_table: unify::Table::new(),
        }
    }

    /// Record a node's synthesized type and return it. The type is stored
    /// as-is (any unbound `Ty::Var` is left intact); a final `resolve_deep`
    /// pass in `run()` substitutes every bound Var once all unification is
    /// done. Recording at call time — rather than resolving here — avoids
    /// re-walking the whole type table on every node, and a node recorded
    /// before its Var is bound (e.g. a generic callee) is still resolved by
    /// that final pass.
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
        //
        // Resolve `expected` through the unification table first so a `Var`
        // that's been bound to `Scalar(0)` by an outer bidirectional Call
        // flow (see `check_call` below) is seen as its concrete shape here.
        // Without this, `Mk(1)` against `Box<Scalar>` wouldn't widen at the
        // arg position because the per-arg `expected` is `Var(α)`, not
        // `Scalar(0)`.
        let resolved_expected = self.unify_table.resolve(expected);
        if let (ExprKind::IntLit(_), Ty::Scalar(d)) = (&e.kind, &resolved_expected)
            && d.is_dimensionless()
        {
            let ty = Ty::Scalar(Dimension::ZERO);
            return self.record(e.id, ty);
        }
        // Bidirectional Call: route `Call` exprs through `check_call` so
        // outer `expected` unifies with the callee's return type BEFORE
        // per-arg checking. This propagates outer constraints into
        // type-Vars introduced by `instantiate_variant_schema`, enabling
        // arg-position widening (e.g. `Mk(1): Box<Scalar>` → α=Scalar
        // first, then the per-arg IntLit-gate fires).
        if let ExprKind::Call(callee, args) = &e.kind {
            return self.check_call(e, callee, args, expected);
        }
        let synthesized = self.synth_expr(e);
        // Q10 (spec §4.7): in an expected-type context whose destination is a
        // unit-annotated `Scalar<u>`, a dimensionless numeric LITERAL (an
        // `IntLit`, a `FloatLit`, or a negated literal) is promoted to
        // `Scalar<u>` — the annotation fixes the unit unambiguously. The
        // IntLit→dimensionless-Scalar widening above covers the `u == ZERO`
        // case; this covers `u != ZERO`.
        //
        // Q10-refinement (2026-05-24): the coercion is LITERAL-ONLY. A
        // dimensionless variable or computed expression (`is_numeric_literal`
        // false) falls through to `unify_or_diag` and is rejected — coercing
        // it would silently turn e.g. a count into a mass across a function
        // boundary. Only fires when an expected type is supplied — bare
        // subexpressions (e.g. the `+` in `1.5 + mass`) are synthesized
        // without an expected type and still reject a dimension mismatch.
        //
        // The `is_numeric_literal(e)` gate is sufficient on its own: a numeric
        // literal always synthesizes to `Int` or a dimensionless `Scalar`
        // (literals carry no unit), so no separate synthesized-type check is
        // needed to know the source is dimensionless.
        if let Ty::Scalar(u) = &resolved_expected
            && !u.is_dimensionless()
            && is_numeric_literal(e)
        {
            return self.record(e.id, resolved_expected.clone());
        }
        // Q10 (Vec): the same expected-type-context promotion for a
        // dimensionless `Vec<n>` literal whose destination is `Vec<n, u>`
        // (u != ZERO) — e.g. `let v: Vec<3, m/s> = [1.0, 2.0, 3.0]`. The
        // length must match (a shape mismatch still diagnoses), and only a
        // unit-less source coerces (`Vec<n, m>` → `Vec<n, kg>` stays a
        // mismatch). No Int→Vec promotion: there is no scalar-to-vector widen.
        //
        // Q10-refinement: LITERAL-ONLY here too, and (unlike a scalar literal)
        // a `VecLit`'s *elements* are checked individually — every element
        // must be a numeric literal. `[1.0, 2.0, 3.0]` coerces; `[a, b, c]`
        // (dimensionless `Scalar` variables) does NOT — otherwise it would
        // launder variables into a unit-annotated `Vec`, the same hole the
        // scalar side closes.
        if let Ty::Vec(en, eu) = &resolved_expected
            && !eu.is_dimensionless()
            && matches!(&e.kind, ExprKind::VecLit(elems) if elems.iter().all(is_numeric_literal))
            && let Ty::Vec(sn, sd) = &synthesized
            && sn == en
            && sd.is_dimensionless()
        {
            return self.record(e.id, resolved_expected.clone());
        }
        self.unify_or_diag(&synthesized, expected, e.span);
        synthesized
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
                    self.definitions,
                    base.span,
                    "field access",
                    &base_ty,
                ));
                Ty::Error
            }
        }
    }

    fn unify_or_diag(&mut self, actual: &Ty, expected: &Ty, span: Span) {
        // Run structural unification — this both compares and BINDS Vars.
        // PR-3b's resolve+compare worked because all types were concrete;
        // PR-3c's variant instantiation introduces Vars whose binding has
        // to flow through the unification table. `unify_table.unify`
        // returns Err on outermost mismatch (with already-resolved Tys);
        // Err's two Tys are then formatted into the user-facing diagnostic.
        // `Ty::Error` unifies with anything, so cascade suppression works.
        if let Err((actual_resolved, expected_resolved)) = self.unify_table.unify(actual, expected)
        {
            self.diagnostics.push(crate::sema::diag::type_mismatch_full(
                self.definitions,
                span,
                &expected_resolved,
                &actual_resolved,
            ));
        }
    }

    fn check_function(&mut self, f: &FunctionDef) {
        // Look up the function's DefId via its AST NodeId. For a *duplicate*
        // top-level function, the resolver's `define_or_report` returns
        // `None` and never inserts into `binding_def_ids`, so this lookup
        // also returns `None` for the duplicate's `f.id` — skipping the
        // body walk so we don't cascade a spurious "expected T, found U"
        // on top of the resolver's `duplicate_name` diag.
        let Some(def_id) = self.binding_def_ids.get(&f.id).copied() else {
            return;
        };
        let expected_return = self.def_types.get(&def_id).and_then(|sig| match sig {
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
                // Recover the local let's DefId via the wrapping `Stmt`'s
                // NodeId (which `define_or_report` keyed the binding entry
                // under). Pass 1 (signature_pass) only handled top-level
                // lets, so the entry may not yet be in def_types; insert it
                // now using the lowered annotation.
                if let Some(def_id) = self.binding_def_ids.get(&s.id).copied() {
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
                self.synth_for(for_stmt);
                Ty::Error
            }
            StmtKind::While(w) => {
                self.synth_while(w);
                Ty::Error
            }
        }
    }

    /// Recover a loop-variable's DefId from its binding-intro NodeId.
    fn loop_var_def_id(&self, binding_id: NodeId) -> Option<DefId> {
        self.binding_def_ids.get(&binding_id).copied()
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
            self.diagnostics.push(crate::sema::diag::non_bool_condition(
                self.definitions,
                cond.span,
                &cond_ty,
            ));
        }
    }

    fn synth_while(&mut self, w: &WhileStmt) {
        self.check_cond(&w.cond);
        self.synth_block(&w.body);
    }

    fn synth_for(&mut self, f: &ForStmt) {
        match f {
            ForStmt::Range {
                var_id,
                start,
                end,
                body,
                ..
            } => {
                self.check_expr(start, &Ty::Int);
                self.check_expr(end, &Ty::Int);
                if let Some(loop_def_id) = self.loop_var_def_id(*var_id) {
                    self.def_types.insert(loop_def_id, Ty::Int);
                }
                self.synth_block(body);
            }
            ForStmt::Iter {
                var_id, iter, body, ..
            } => {
                let iter_ty = self.synth_expr(iter);
                let elem_ty = match &iter_ty {
                    Ty::Array(t) => (**t).clone(),
                    Ty::Vec(_, dim) => Ty::Scalar(*dim),
                    Ty::Error => Ty::Error,
                    other => {
                        self.diagnostics.push(crate::sema::diag::op_type_error(
                            self.definitions,
                            iter.span,
                            "for-in iteration",
                            other,
                        ));
                        Ty::Error
                    }
                };
                if let Some(loop_def_id) = self.loop_var_def_id(*var_id) {
                    self.def_types.insert(loop_def_id, elem_ty);
                }
                self.synth_block(body);
            }
            ForStmt::IterKV {
                key_id,
                value_id,
                iter,
                body,
                ..
            } => {
                let iter_ty = self.synth_expr(iter);
                let (k_ty, v_ty) = match &iter_ty {
                    Ty::Dict(k, v) => ((**k).clone(), (**v).clone()),
                    Ty::Error => (Ty::Error, Ty::Error),
                    other => {
                        self.diagnostics.push(crate::sema::diag::op_type_error(
                            self.definitions,
                            iter.span,
                            "for-key-value iteration",
                            other,
                        ));
                        (Ty::Error, Ty::Error)
                    }
                };
                if let Some(k_def_id) = self.loop_var_def_id(*key_id) {
                    self.def_types.insert(k_def_id, k_ty);
                }
                if let Some(v_def_id) = self.loop_var_def_id(*value_id) {
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
                    row.len(),
                ));
                // Bail on shape mismatch to keep the no-cascade invariant.
                return Ty::Error;
            }
            for cell in row {
                let cell_ty = self.synth_expr(cell);
                if !matches!(cell_ty, Ty::Int | Ty::Scalar(_) | Ty::Error) {
                    self.diagnostics.push(crate::sema::diag::op_type_error(
                        self.definitions,
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
                    self.definitions,
                    base.span,
                    "indexing",
                    &other,
                ));
                Ty::Error
            }
        }
    }
}

/// True if `e` is a numeric literal eligible for Q10 literal-to-unit coercion
/// — a bare `IntLit` / `FloatLit`, or one negated by a unary minus (`-1.5`,
/// parsed as `Neg(FloatLit)`). Per the Q10-refinement (2026-05-24), only
/// literals coerce into a unit-annotated `Scalar<u>`; a dimensionless variable
/// or computed expression is rejected, closing the units-safety hole where a
/// count could silently become a mass across a function boundary
/// (`function mass_of(n: Int): Scalar<kg> return n end`).
fn is_numeric_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) => true,
        ExprKind::UnaryOp(UnaryOp::Neg, inner) => {
            matches!(inner.kind, ExprKind::IntLit(_) | ExprKind::FloatLit(_))
        }
        _ => false,
    }
}

pub(crate) fn run(
    program: &Program,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    binding_def_ids: &BindingTable,
    def_types: &mut HashMap<DefId, Ty>,
    struct_fields: &HashMap<DefId, Vec<(String, Ty)>>,
    variant_payloads: &HashMap<DefId, VariantPayload>,
) -> (HashMap<NodeId, Ty>, Vec<Diagnostic>) {
    let mut tc = TypeChecker::new(
        resolutions,
        definitions,
        binding_def_ids,
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

    // §1078: close the Var-leak. A node's type is recorded the moment it is
    // synthesized, but a unification `Var` it embeds may only be bound later
    // (e.g. a generic constructor's callee node is recorded before its
    // argument unifies the type-arg Var). A single final `resolve_deep` pass
    // — run after every body is checked, so all bindings are in place —
    // guarantees `TypedProgram.types` carries no unresolved `Var`. Resolving
    // at record time would miss any Var bound after the record.
    //
    // Invariant assumption: every `Var` is bound by end-of-check. This holds
    // given dyne's mandatory annotations (let / param / return types are
    // never inferred) + per-use-site Var minting (`instantiate_variant_schema`
    // mints a fresh batch per constructor reference, each constrained by its
    // call), so no Var escapes under-constrained in well-formed input. A
    // genuinely-unbound residual Var (an under-constrained generic that no
    // context pins) would be left as-is here, NOT diagnosed — emitting an
    // "ambiguous type / annotation needed" diagnostic for residual Vars is
    // deferred to PR-3e+. `resolve_deep` returns such a Var unchanged, so the
    // worst case is an unresolved Var in `types`, never a panic or hang.
    let resolved_types = tc
        .types
        .iter()
        .map(|(id, ty)| (*id, tc.unify_table.resolve_deep(ty)))
        .collect();
    (resolved_types, tc.diagnostics)
}

#[cfg(test)]
pub(crate) mod test_support {
    use crate::lexer::tokenize;
    use crate::parser::parse;
    use crate::sema::check;

    pub(crate) fn compile_src(src: &str) {
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let _typed = check(prog).expect("ok");
    }

    pub(crate) fn diags_for(src: &str) -> Vec<crate::diag::Diagnostic> {
        let prog = parse(tokenize(src).unwrap()).unwrap();
        check(prog).expect_err("expected diags")
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::{compile_src, diags_for};
    use crate::lexer::tokenize;
    use crate::parser::parse;
    use crate::sema::check;

    #[test]
    fn synth_int_literal_in_function_body_succeeds() {
        compile_src("function f(): Int\n  return 42\nend");
    }

    #[test]
    fn check_int_literal_against_scalar_zero_succeeds() {
        compile_src("let x: Scalar = 5");
    }

    #[test]
    fn struct_name_appears_in_type_mismatch_message() {
        let diags = diags_for("struct P\n  x: Scalar\nend\nfunction f(p: P): Int\n  return p\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert!(
            diags[0].message.contains("found `P`"),
            "message: {}",
            diags[0].message
        );
    }

    #[test]
    fn return_value_type_mismatch_diag() {
        let diags = diags_for("function f(): Int\n  return true\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("type mismatch"));
    }

    // ----- PR-3b Task 5: call / struct literal / field access -----

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

    // ----- Task 8 (post-/review fix loop): G1 / G2 / G3 regression tests -----

    #[test]
    fn typed_program_types_contains_no_unresolved_vars() {
        // §1078 invariant: after check completes, no TypedProgram.types entry
        // may contain a Ty::Var anywhere in its structure.
        //
        // A generic variant construction (`Just(1)`) mints a fresh type-arg
        // Var that unification binds to Int. Two nodes record types built from
        // that Var: the call result (`Just(1)` → Enum(Maybe, [Var])) and — the
        // tricky one — the callee node (`Just` → Function([Var], Enum(Maybe,
        // [Var]))), which is recorded *before* the arg unifies the Var. Only a
        // final resolve pass (after all bindings) catches both; resolving at
        // record time would miss the callee. This regression pins that both
        // are fully resolved.
        use crate::sema::ty::Ty;
        let src = "enum Maybe<T>\n  Just(T)\n  Nothing\nend\n\
                   function f(): Maybe<Int>\n  return Just(1)\nend";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let typed = check(prog).expect("clean compile");

        fn contains_var(t: &Ty) -> bool {
            match t {
                Ty::Var(_) => true,
                Ty::Function(args, ret) => args.iter().any(contains_var) || contains_var(ret),
                Ty::Enum(_, args) => args.iter().any(contains_var),
                Ty::Array(t) => contains_var(t),
                Ty::Dict(k, v) => contains_var(k) || contains_var(v),
                // Int / Scalar / Bool / String / Vec / Mat / Struct / Param /
                // Error carry no nested Ty, so none can hide a Var.
                _ => false,
            }
        }

        for (id, ty) in typed.types.iter() {
            assert!(!contains_var(ty), "Ty::Var leaked at {id:?}: {ty:?}");
        }
    }

    #[test]
    fn duplicate_top_level_function_does_not_cascade_to_first_body() {
        // G3: when two top-level items share a name, the resolver emits
        // `duplicate_name` and re-uses the first DefId. signature_pass
        // previously overwrote `def_types[def_id]` with the second def's
        // signature, causing `check_function` for the FIRST body to type-
        // check against the wrong return type and emit a spurious second
        // diag. The first-writer-wins gate keeps the first signature so
        // the body remains consistent with its declared signature.
        let diags =
            diags_for("function f(): Int\n  return 0\nend\nfunction f(): Bool\n  return true\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("already defined") || diags[0].message.contains("duplicate"),
            "msg: {}",
            diags[0].message
        );
    }
}
