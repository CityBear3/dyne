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
    BinOp, Block, Expr, ExprKind, ForStmt, FunctionDef, IfExpr, Item, MatchArm, Pattern,
    PatternKind, Program, Stmt, StmtKind, UnaryOp, WhileStmt,
};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{BindingTable, DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{Dimension, Ty, VariantPayload, lower_type};
use crate::sema::unify;
use crate::source::Span;

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
        self.unify_or_diag(&synthesized, expected, e.span);
        synthesized
    }

    /// Bidirectional check for `Call` expressions. Mirrors `synth_call`'s
    /// arity / arg-type / not-callable diagnostics, but pre-unifies the
    /// callee's return type with the outer `expected` so type-Vars in the
    /// signature pick up outer constraints before per-arg checking.
    fn check_call(&mut self, e: &Expr, callee: &Expr, args: &[Expr], expected: &Ty) -> Ty {
        let callee_ty = self.synth_expr(callee);
        let resolved = self.unify_table.resolve(&callee_ty);
        let result = match resolved {
            Ty::Error => Ty::Error,
            Ty::Function(param_tys, ret_ty) => {
                // Step 1: silently bind `ret_ty` against the outer
                // expected. Final `unify_or_diag` below catches any
                // mismatch that survives — Err here would be redundant.
                let _ = self.unify_table.unify(&ret_ty, expected);
                if param_tys.len() != args.len() {
                    self.diagnostics.push(crate::sema::diag::wrong_arity(
                        e.span,
                        param_tys.len(),
                        args.len(),
                    ));
                    // Suppress cascade — wrong_arity already pinned the
                    // structural error; the outer `unify_or_diag` would
                    // otherwise pile a "type mismatch" on top.
                    Ty::Error
                } else {
                    for (arg, p_ty) in args.iter().zip(param_tys.iter()) {
                        self.check_expr(arg, p_ty);
                    }
                    *ret_ty
                }
            }
            other => {
                self.diagnostics
                    .push(crate::sema::diag::not_callable(callee.span, &other));
                Ty::Error
            }
        };
        // Final unify catches surviving mismatches (e.g. wrong arg type
        // didn't bind a Var the outer expected required). `Ty::Error`
        // unifies with anything so the no-cascade arity / not-callable
        // paths don't fire a second diag.
        self.unify_or_diag(&result, expected, e.span);
        self.record(e.id, result)
    }

    fn synth_ident(&mut self, e: &Expr) -> Ty {
        let Some(def_id) = self.resolutions.get(&e.id).copied() else {
            return Ty::Error; // resolver already reported
        };
        if let Some(ty) = self.def_types.get(&def_id).cloned() {
            // Enum-variant schemas may carry `Ty::Param(i)` sentinels from
            // signature_pass. Instantiate with fresh `Ty::Var`s per use
            // site so two references to the same variant get independent
            // inference variables — `Just(1)` and `Just("x")` in different
            // contexts must not share a single Var (which would conflict).
            if self.is_variant_def(def_id) {
                return self.instantiate_variant_schema(def_id, &ty);
            }
            return ty;
        }
        // Definition exists but no `def_types` entry: type-level definition
        // (Struct / Enum) used as a value gets a focused diagnostic. Other
        // kinds (e.g. orphan EnumVariant — shouldn't happen post-Task-3)
        // fall through to silent Ty::Error so the no-cascade invariant
        // holds.
        if let Some(info) = self.definitions.get(&def_id) {
            match info.kind {
                DefKind::Struct | DefKind::Enum => {
                    let name = info.name.clone();
                    let kind = info.kind;
                    self.diagnostics
                        .push(crate::sema::diag::not_a_value(e.span, kind, &name));
                }
                _ => {}
            }
        }
        Ty::Error
    }

    /// True if `def_id` is an enum variant. Used by `synth_ident` to gate
    /// schema instantiation.
    fn is_variant_def(&self, def_id: DefId) -> bool {
        self.definitions
            .get(&def_id)
            .is_some_and(|info| matches!(info.kind, DefKind::EnumVariant))
    }

    /// Walk the variant's parent enum to count its type-parameter arity,
    /// allocate that many fresh `Ty::Var`s, then substitute every
    /// `Ty::Param(i)` in the schema with the corresponding fresh Var.
    /// Non-generic variants (parent type_params is empty) short-circuit
    /// to the schema unchanged — no allocation, no walk.
    fn instantiate_variant_schema(&mut self, variant_def_id: DefId, schema: &Ty) -> Ty {
        let n_params = self
            .variant_payloads
            .get(&variant_def_id)
            .and_then(|vp| self.definitions.get(&vp.parent_enum))
            .map(|info| info.type_params.len())
            .unwrap_or(0);
        if n_params == 0 {
            return schema.clone();
        }
        let type_args: Vec<Ty> = (0..n_params)
            .map(|_| Ty::Var(self.unify_table.fresh()))
            .collect();
        schema.subst_with_args(&type_args)
    }

    fn synth_binop(&mut self, op: BinOp, l: &Expr, r: &Expr) -> Ty {
        let lt = self.synth_expr(l);
        let rt = self.synth_expr(r);
        if matches!(lt, Ty::Error) || matches!(rt, Ty::Error) {
            return Ty::Error;
        }
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                self.synth_arith(op, &lt, &rt, l.span)
            }
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
                // Vec/Mat negation is valid dyne. The result type is
                // approximate (true unit propagation lands in PR-3d under
                // Option β: silent ZERO-strip per design memo); returning
                // the input type rather than `Ty::Error` lets cross-context
                // unification surface accurate "expected T, found Vec/Mat"
                // diagnostics instead of silently swallowing them.
                Ty::Vec(n, d) => Ty::Vec(*n, *d),
                Ty::Mat(m, n) => Ty::Mat(*m, *n),
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

    /// Arithmetic on `Int` / `Scalar` / `Vec` / `Mat`.
    ///
    /// Scalar/Int dimension propagation (Q4): `Int` promotes to a
    /// dimensionless `Scalar` in mixed contexts; `+`/`-` require equal
    /// dimensions (else `dimension_mismatch`); `*` / `/` compute
    /// `d1.mul(d2)` / `d1.div(d2)` (overflow → `dimension_overflow`); pure
    /// `Int op Int` stays `Int` (integer division for `/`, Q4-2).
    ///
    /// Vec/Mat operands keep the PR-3b/3c placeholder for now: the result
    /// is the operand's shape (NOT `Ty::Error`) so cross-context
    /// unification still surfaces accurate "expected T, found Vec/Mat"
    /// diagnostics (pinned by `vec_add_in_int_context_emits_diag`). Real
    /// Q5 / Q6 Vec / Mat rules replace these arms in Tasks 3-4.
    fn synth_arith(&mut self, op: BinOp, l: &Ty, r: &Ty, l_span: Span) -> Ty {
        // Q9 (CQ M4 from α /review): short-circuit on `Ty::Error` so a
        // failed-lowering operand can't masquerade as a dimensionless
        // `Scalar` and emit a misleading dimension_mismatch. `synth_binop`
        // already guards this; the entry check keeps `synth_arith` correct
        // for any caller, per Q9's "short-circuit at all synth_* entries".
        if matches!(l, Ty::Error) || matches!(r, Ty::Error) {
            return Ty::Error;
        }

        // Q4 Step 1: promote `Int` to dimensionless `Scalar` in mixed pairs.
        let (l_eff, r_eff) = promote_int_to_scalar(l, r);

        match (op, &l_eff, &r_eff) {
            // Pure Int op Int → Int (integer division for `/`, Q4-2).
            (_, Ty::Int, Ty::Int) => Ty::Int,

            // Scalar +/- Scalar: dimensions must match (Q4 Step 2).
            (BinOp::Add | BinOp::Sub, Ty::Scalar(d1), Ty::Scalar(d2)) => {
                if d1 == d2 {
                    Ty::Scalar(*d1)
                } else {
                    self.diagnostics.push(crate::sema::diag::dimension_mismatch(
                        l_span,
                        op_symbol(op),
                        &l_eff,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Scalar * Scalar / Scalar: dimension arithmetic.
            (BinOp::Mul, Ty::Scalar(d1), Ty::Scalar(d2)) => match d1.mul(*d2) {
                Ok(d) => Ty::Scalar(d),
                Err(_) => {
                    self.diagnostics
                        .push(crate::sema::diag::dimension_overflow(l_span));
                    Ty::Error
                }
            },
            (BinOp::Div, Ty::Scalar(d1), Ty::Scalar(d2)) => match d1.div(*d2) {
                Ok(d) => Ty::Scalar(d),
                Err(_) => {
                    self.diagnostics
                        .push(crate::sema::diag::dimension_overflow(l_span));
                    Ty::Error
                }
            },

            // Mat: PR-3b/3c placeholder (shape preserved). Mat takes
            // precedence over Vec when both appear (so Mat·Vec stays on the
            // placeholder until Task 4's Q6 rules land). Replaced in Task 4.
            (_, Ty::Mat(m, n), _) | (_, _, Ty::Mat(m, n)) => Ty::Mat(*m, *n),

            // Q5: Vec rules.
            //
            // Vec +/- Vec: same shape AND same dim. Shape is checked first
            // so a shape-and-dim double mismatch yields a single (shape)
            // diagnostic, no cascade (Q5-4).
            (BinOp::Add | BinOp::Sub, Ty::Vec(n1, d1), Ty::Vec(n2, d2)) => {
                if n1 != n2 {
                    self.diagnostics
                        .push(crate::sema::diag::shape_mismatch_vec(l_span, *n1, *n2));
                    Ty::Error
                } else if d1 != d2 {
                    self.diagnostics.push(crate::sema::diag::dimension_mismatch(
                        l_span,
                        op_symbol(op),
                        &l_eff,
                        &r_eff,
                    ));
                    Ty::Error
                } else {
                    Ty::Vec(*n1, *d1)
                }
            }

            // Vec * Scalar / Scalar * Vec (commutative): dim multiplied.
            (BinOp::Mul, Ty::Vec(n, dv), Ty::Scalar(ds))
            | (BinOp::Mul, Ty::Scalar(ds), Ty::Vec(n, dv)) => match dv.mul(*ds) {
                Ok(d) => Ty::Vec(*n, d),
                Err(_) => {
                    self.diagnostics
                        .push(crate::sema::diag::dimension_overflow(l_span));
                    Ty::Error
                }
            },

            // Vec / Scalar: dim divided. (Scalar / Vec is rejected below.)
            (BinOp::Div, Ty::Vec(n, dv), Ty::Scalar(ds)) => match dv.div(*ds) {
                Ok(d) => Ty::Vec(*n, d),
                Err(_) => {
                    self.diagnostics
                        .push(crate::sema::diag::dimension_overflow(l_span));
                    Ty::Error
                }
            },

            // Every other Vec involvement is rejected: Vec*Vec, Vec/Vec,
            // Vec +/- Scalar (broadcasting), Scalar / Vec, etc.
            (_, Ty::Vec(_, _), _) | (_, _, Ty::Vec(_, _)) => {
                self.diagnostics.push(crate::sema::diag::type_mismatch(
                    l_span,
                    "Vec operation not supported for these operands (Vec +/- Vec requires equal shape and dimension; use dot()/cross() for vector products; Vec scales by Scalar only)",
                ));
                Ty::Error
            }

            _ => {
                self.diagnostics.push(crate::sema::diag::type_mismatch(
                    l_span,
                    "arithmetic operands must both be Int or Scalar",
                ));
                Ty::Error
            }
        }
    }

    /// Pow: base must be `Int` / `Scalar` / `Vec` / `Mat`; exponent must
    /// be `Int`. Vec/Mat semantics (element-wise vs. linear-algebra power)
    /// land in PR-3d-β.
    ///
    /// Slice boundary: we strip dim across both Scalar and Vec arms here
    /// so the operator-side is uniform (`synth_pow` returns `ZERO` for
    /// every shape that can carry a dim). `synth_arith`'s Vec/Mat arm is
    /// asymmetric — it preserves the operand's `Dimension` because Vec
    /// arithmetic in α is a non-Error placeholder for cross-context
    /// unification (β re-routes it through unify with real propagation).
    /// Preserving the input dim *here* would leak it into return-type
    /// unify and surface a confused "expected `Scalar`, found `Scalar`"
    /// diag once PR-3d-α annotations carry real dims.
    fn synth_pow(&mut self, l: &Ty, r: &Ty, l_span: Span, r_span: Span) -> Ty {
        let result = match l {
            Ty::Int => Ty::Int,
            Ty::Scalar(_) => Ty::Scalar(Dimension::ZERO),
            Ty::Vec(n, _) => Ty::Vec(*n, Dimension::ZERO),
            Ty::Mat(m, n) => Ty::Mat(*m, *n),
            _ => Ty::Error,
        };
        if !matches!(r, Ty::Int) {
            self.diagnostics
                .push(crate::sema::diag::op_type_error(r_span, "`^` exponent", r));
        }
        if matches!(result, Ty::Error) {
            self.diagnostics
                .push(crate::sema::diag::op_type_error(l_span, "`^` base", l));
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
                self.synth_for(for_stmt, s.span);
                Ty::Error
            }
            StmtKind::While(w) => {
                self.synth_while(w);
                Ty::Error
            }
        }
    }

    /// Recover a loop-variable's DefId by `(DefKind::LoopVar, name, span)`.
    /// Loop vars are the lone holdout from `binding_def_ids`: `ForStmt`'s
    /// AST has no per-binding NodeId, so the resolver passes `None` to
    /// `define_or_report` and this linear scan stands in. TODO: when
    /// `ForStmt` grows per-binding NodeIds, replace with a
    /// `binding_def_ids.get(&node_id).copied()` lookup.
    fn loop_var_def_id(&self, name: &str, span: Span) -> Option<DefId> {
        self.definitions
            .iter()
            .find(|(_, info)| {
                matches!(info.kind, DefKind::LoopVar) && info.name == name && info.span == span
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
        // Exhaustiveness check (Task 7). Resolve the scrutinee type
        // through the unification table first so any Vars bound by
        // arm-pattern flow are seen as their concrete instantiation —
        // a `Maybe<Var(α)>` becomes `Maybe<Int>` once an arm pattern's
        // payload binds α=Int, and exhaustiveness can then substitute
        // payload params correctly.
        //
        // `resolve_deep` (rather than plain `resolve`) is required for
        // inline-constructed scrutinees like `match Some(Some(1)) ...`:
        // the outer Option's type-arg is a still-unbound Var at the
        // top level, but the inner Var has been bound to `Int` by the
        // inner constructor's argument unification. Without the deep
        // walk, the inner column's substituted payload type would be
        // `Var(α)` and exhaust would fall into its sentinel skip arm,
        // silently accepting a non-exhaustive nested pattern set.
        let resolved_scrut = self.unify_table.resolve_deep(&scrut_ty);
        let exhaust_diags = crate::sema::exhaust::check_exhaustive(
            &resolved_scrut,
            arms,
            scrutinee.span,
            self.resolutions,
            self.definitions,
            self.variant_payloads,
        );
        self.diagnostics.extend(exhaust_diags);

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
            PatternKind::Ident(_name) => {
                // Pattern bindings are introductions (not uses), so they're
                // recorded in `binding_def_ids` keyed by the pattern's own
                // NodeId rather than in `resolutions`. Recover the DefId in
                // O(1) and record its type as the scrutinee's.
                if let Some(def_id) = self.binding_def_ids.get(&p.id).copied() {
                    self.def_types.insert(def_id, expected.clone());
                }
            }
            PatternKind::Variant(name, sub_patterns) => {
                let Some(variant_def_id) = self.resolutions.get(&p.id).copied() else {
                    return; // resolver already reported
                };
                let Some(variant_info) = self.variant_payloads.get(&variant_def_id).cloned() else {
                    return;
                };
                // Resolve the expected (scrutinee) type — it may carry Vars
                // bound by the outer match's bidirectional flow. We need a
                // concrete `Ty::Enum(parent, type_args)` to validate the
                // variant and substitute its payload.
                let resolved_expected = self.unify_table.resolve(expected);
                let (parent, type_args) = match &resolved_expected {
                    Ty::Enum(parent, args) => (*parent, args.clone()),
                    Ty::Error => return, // no-cascade
                    other => {
                        // Pattern fired against a scrutinee whose type isn't
                        // an enum — e.g. `match 1 { case Some(x) => ... }`.
                        self.diagnostics
                            .push(crate::sema::diag::pattern_type_mismatch(
                                p.span, other, "enum",
                            ));
                        return;
                    }
                };
                if variant_info.parent_enum != parent {
                    self.diagnostics
                        .push(crate::sema::diag::wrong_variant_for_enum(
                            p.span,
                            name,
                            &resolved_expected,
                        ));
                    return;
                }
                // Substitute Param(i) → type_args[i] in the payload schema.
                // For non-generic enums type_args is empty and substitution
                // is identity (no Param positions in the payload).
                let substituted: Vec<Ty> = variant_info
                    .payload
                    .iter()
                    .map(|t| t.subst_with_args(&type_args))
                    .collect();
                if sub_patterns.len() != substituted.len() {
                    self.diagnostics.push(crate::sema::diag::wrong_arity(
                        p.span,
                        substituted.len(),
                        sub_patterns.len(),
                    ));
                    return;
                }
                for (sub, sub_ty) in sub_patterns.iter().zip(substituted.iter()) {
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
                    row.len(),
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

/// Q4 Step 1 (+ Q11): in a mixed binary op, an `Int` operand promotes to a
/// dimensionless `Scalar` so the Scalar/Vec rules handle it uniformly:
/// - `Int op Scalar` → `Scalar + Scalar<kg>` so `Int + Scalar<kg>` becomes a
///   `dimension_mismatch` (Q4-1) while `Int + Scalar` (dimensionless) succeeds.
/// - `Int op Vec` (Q11=A: Int scales Vec) → `Scalar op Vec`, so `2 * v` /
///   `v * 2` / `v / 2` route through the commutative `Vec * Scalar` and
///   `Vec / Scalar` arms (`ZERO.mul(d)=d`, `d.div(ZERO)=d`, leaving the unit
///   unchanged); `2 + v` falls through to the Vec reject arm as `Scalar + Vec`.
///
/// `Int op Mat` is intentionally NOT promoted here — Mat rules are a
/// placeholder until Task 4, which extends this for `Mat` scaling.
/// Non-mixed pairs pass through unchanged.
fn promote_int_to_scalar(l: &Ty, r: &Ty) -> (Ty, Ty) {
    match (l, r) {
        (Ty::Int, Ty::Scalar(_) | Ty::Vec(_, _)) => (Ty::Scalar(Dimension::ZERO), r.clone()),
        (Ty::Scalar(_) | Ty::Vec(_, _), Ty::Int) => (l.clone(), Ty::Scalar(Dimension::ZERO)),
        _ => (l.clone(), r.clone()),
    }
}

/// Render a binary operator as its source symbol for operator-focus
/// diagnostics (e.g. `dimension_mismatch`).
fn op_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
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

    // ----- PR-3d-β Task 2: synth_arith Scalar/Int dimension rules (Q4) -----
    //
    // Dim-carrying Scalars are supplied via function *parameters* (not
    // `let a: Scalar<kg> = 1.0`) because literal-to-unit coercion is Task 10
    // (executes after this task). Params give the operands their annotated
    // dimension without tripping the deferred coercion gap — mirroring the
    // α convention documented in sema.rs.

    #[test]
    fn arith_int_int_add_returns_int() {
        compile_src("function f(): Int\n  return 1 + 2\nend");
    }

    #[test]
    fn arith_scalar_kg_plus_scalar_kg_returns_scalar_kg() {
        // Same dim → result Scalar<kg>, unifies with the declared return.
        compile_src("function f(a: Scalar<kg>, b: Scalar<kg>): Scalar<kg>\n  return a + b\nend");
    }

    #[test]
    fn arith_scalar_kg_plus_scalar_m_dim_mismatch_diag() {
        let diags =
            diags_for("function f(a: Scalar<kg>, b: Scalar<m>): Scalar<kg>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension mismatch in '+': left side has Scalar<kg>, but right side has Scalar<m>"
        );
    }

    #[test]
    fn arith_int_plus_scalar_dimensionless_widens() {
        // Int + Scalar(ZERO): Int promotes to Scalar(ZERO), ZERO == ZERO.
        compile_src("function f(x: Scalar): Scalar\n  return 1 + x\nend");
    }

    #[test]
    fn arith_int_plus_scalar_kg_dim_mismatch_diag() {
        // Q4-1: Int promotes to Scalar(ZERO); ZERO != kg → dimension_mismatch.
        // The left side renders as bare `Scalar` (dimensionless, the promoted
        // Int) rather than `Int` — Q7-A routes Int→Scalar conversion failures
        // through dimension_mismatch, so "Scalar vs Scalar<kg>" faithfully
        // reflects the type system's reasoning. Lock that rendering in.
        let diags = diags_for("function f(x: Scalar<kg>): Scalar<kg>\n  return 1 + x\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension mismatch in '+': left side has Scalar, but right side has Scalar<kg>"
        );
    }

    #[test]
    fn arith_scalar_kg_mul_scalar_m_returns_kg_times_m() {
        // d1.mul(d2): kg * m → kg*m.
        compile_src("function f(a: Scalar<kg>, b: Scalar<m>): Scalar<kg*m>\n  return a * b\nend");
    }

    #[test]
    fn arith_scalar_kg_div_scalar_s_returns_kg_per_s() {
        // d1.div(d2): kg / s → kg/s.
        compile_src("function f(a: Scalar<kg>, b: Scalar<s>): Scalar<kg/s>\n  return a / b\nend");
    }

    #[test]
    fn arith_int_int_div_returns_int() {
        // Q4-2: Int / Int = Int (integer division).
        compile_src("function f(): Int\n  return 5 / 2\nend");
    }

    #[test]
    fn arith_int_mul_scalar_kg_propagates_dim() {
        // Spec §4.7: i * dt produces Scalar<dt's dim>. Int promotes to ZERO,
        // ZERO * kg = kg → Scalar<kg>.
        compile_src("function f(dt: Scalar<kg>): Scalar<kg>\n  return 5 * dt\nend");
    }

    // ----- PR-3d-β Task 3: synth_arith Vec rules (Q5) -----
    //
    // Dim-carrying Vecs are supplied via params (not `let a: Vec<3, m> = [..]`)
    // for the same Task-10 coercion reason as the Q4 tests above.

    #[test]
    fn vec_add_same_shape_same_dim_returns_vec() {
        compile_src("function f(a: Vec<3, m>, b: Vec<3, m>): Vec<3, m>\n  return a + b\nend");
    }

    #[test]
    fn vec_add_shape_mismatch_diag() {
        let diags = diags_for("function f(a: Vec<3>, b: Vec<2>): Vec<3>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "Vec shape mismatch: left side has length 3, but right side has length 2"
        );
    }

    #[test]
    fn vec_add_dim_mismatch_diag() {
        let diags =
            diags_for("function f(a: Vec<3, m>, b: Vec<3, kg>): Vec<3, m>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension mismatch in '+': left side has Vec<3, m>, but right side has Vec<3, kg>"
        );
    }

    #[test]
    fn vec_shape_first_diag_when_both_mismatch() {
        // Q5-4: shape diag wins, dim diag suppressed (single diag, no cascade).
        let diags =
            diags_for("function f(a: Vec<3, m>, b: Vec<2, kg>): Vec<3, m>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "expected single shape diag, got: {diags:?}");
        // Shape diag only — the dim mismatch (m vs kg) is suppressed (Q5-4).
        assert_eq!(
            diags[0].message,
            "Vec shape mismatch: left side has length 3, but right side has length 2"
        );
    }

    #[test]
    fn vec_mul_scalar_propagates_dim() {
        // Vec<3, m> * Scalar<s> → Vec<3, m*s>.
        compile_src("function f(v: Vec<3, m>, t: Scalar<s>): Vec<3, m*s>\n  return v * t\nend");
    }

    #[test]
    fn scalar_mul_vec_commutative() {
        // Scalar<s> * Vec<3, m> → Vec<3, m*s> (commutative).
        compile_src("function f(v: Vec<3, m>, t: Scalar<s>): Vec<3, m*s>\n  return t * v\nend");
    }

    #[test]
    fn vec_div_scalar_subtracts_dim() {
        // Vec<3, m> / Scalar<s> → Vec<3, m/s>.
        compile_src("function f(v: Vec<3, m>, t: Scalar<s>): Vec<3, m/s>\n  return v / t\nend");
    }

    // The unsupported-Vec-operation reject message, shared by the three
    // rejection cases below (Vec*Vec, Vec+Scalar broadcasting, Scalar/Vec).
    const VEC_REJECT_MSG: &str = "Vec operation not supported for these operands (Vec +/- Vec requires equal shape and dimension; use dot()/cross() for vector products; Vec scales by Scalar only)";

    #[test]
    fn vec_mul_vec_rejected_diag() {
        // Q5-1: Vec*Vec rejected (use dot()/cross()).
        let diags = diags_for("function f(a: Vec<3>, b: Vec<3>): Vec<3>\n  return a * b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, VEC_REJECT_MSG);
    }

    #[test]
    fn vec_plus_scalar_rejected_diag() {
        // Q5-3: Vec + Scalar broadcasting rejected.
        let diags = diags_for("function f(v: Vec<3>, s: Scalar): Vec<3>\n  return v + s\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, VEC_REJECT_MSG);
    }

    #[test]
    fn scalar_div_vec_rejected() {
        // Scalar / Vec rejected (only Vec / Scalar allowed).
        let diags = diags_for("function f(v: Vec<3>, s: Scalar): Vec<3>\n  return s / v\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, VEC_REJECT_MSG);
    }

    // Q11=A: Int scales Vec (promotes to dimensionless Scalar). Scaling by a
    // dimensionless factor leaves the unit unchanged, so the result is the
    // input Vec type — pinned via the return-type unification trick.

    #[test]
    fn int_mul_vec_scales_unit_unchanged() {
        // 2 * v : Int promotes to Scalar(ZERO); ZERO.mul(m) = m → Vec<3, m>.
        compile_src("function f(v: Vec<3, m>): Vec<3, m>\n  return 2 * v\nend");
    }

    #[test]
    fn vec_mul_int_scales_unit_unchanged() {
        // v * 2 : m.mul(ZERO) = m → Vec<3, m>.
        compile_src("function f(v: Vec<3, m>): Vec<3, m>\n  return v * 2\nend");
    }

    #[test]
    fn vec_div_int_scales_unit_unchanged() {
        // v / 2 : m.div(ZERO) = m → Vec<3, m> (dimensionless divisor).
        compile_src("function f(v: Vec<3, m>): Vec<3, m>\n  return v / 2\nend");
    }

    #[test]
    fn scalar_mul_vec_still_works_regression() {
        // Regression: a Scalar (float literal) scaling a Vec is unchanged by
        // the Int-promotion extension — 2.0 * v still yields Vec<3, m>.
        compile_src("function f(v: Vec<3, m>): Vec<3, m>\n  return 2.0 * v\nend");
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

    // ----- Task 8 (post-/review fix loop): G1 / G2 / G3 regression tests -----

    #[test]
    fn struct_name_in_value_position_emits_diag() {
        // G1: `synth_ident` previously returned `Ty::Error` for any DefId
        // without a `def_types` entry, silently swallowing the cross-context
        // mismatch (`Ty::Error` short-circuits `unify_or_diag`). The fix
        // emits a dedicated `not_a_value` diagnostic for `DefKind::Struct`.
        let diags = diags_for(
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nfunction f(): Int\n  return Point\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("`Point`"),
            "msg: {}",
            diags[0].message
        );
        assert!(
            diags[0].message.contains("not a value"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn enum_name_in_value_position_emits_diag() {
        // G1: same as `struct_name_in_value_position_emits_diag` for
        // `DefKind::Enum`. (`DefKind::EnumVariant` continues to silently
        // return `Ty::Error` — variant-as-value typing is a documented
        // PR-3c deferral.)
        let diags = diags_for(
            "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(): Int\n  return Maybe\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("`Maybe`"),
            "msg: {}",
            diags[0].message
        );
        assert!(
            diags[0].message.contains("not a value"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn vec_neg_in_int_context_emits_diag() {
        // G2: `synth_unaryop`'s Neg arm previously returned `Ty::Error` for
        // Vec/Mat, silently swallowing cross-context mismatches. The fix
        // returns the input type so `unify_or_diag` produces the expected
        // "expected Int, found Vec<3>" diagnostic.
        let diags = diags_for("function f(v: Vec<3>): Int\n  return -v\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Int"),
            "msg: {}",
            diags[0].message
        );
        assert!(
            diags[0].message.contains("Vec"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn vec_add_in_int_context_emits_diag() {
        // G2 (broader scope): `synth_arith`'s Vec/Mat arm previously
        // returned `Ty::Error`, silently swallowing cross-context
        // mismatches. After the fix, `Vec + Vec` returns the input Vec
        // shape so the function's `Int` return type triggers an accurate
        // "expected Int, found Vec<3>" diagnostic. Reverting the
        // synth_arith Vec/Mat arms to `Ty::Error` would re-break this.
        let diags = diags_for("function f(v: Vec<3>): Int\n  return v + v\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Int") && diags[0].message.contains("Vec"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn vec_pow_in_int_context_emits_diag() {
        // G2 (broader scope): `synth_pow`'s Vec/Mat arm previously
        // returned `Ty::Error`, silently swallowing cross-context
        // mismatches. After the fix, `Vec ^ Int` returns the input Vec
        // shape so the function's `Int` return type triggers an accurate
        // "expected Int, found Vec<3>" diagnostic. dyne uses `^` for
        // power; reverting the synth_pow Vec/Mat arms to early-return
        // `Ty::Error` would re-break this.
        let diags = diags_for("function f(v: Vec<3>): Int\n  return v ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Int") && diags[0].message.contains("Vec"),
            "msg: {}",
            diags[0].message
        );
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

    // ----- PR-3c Task 4: variant constructor instantiation -----

    #[test]
    fn variant_call_non_generic_typechecks() {
        // Closes PR-3b's silent gap. `Just(1)` is now type-checked: the
        // variant's schema `Function([Int], Enum(maybe, []))` is retrieved
        // by synth_ident, then synth_call checks the arg against `Int`.
        compile_src(
            "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(): Maybe\n  return Just(1)\nend",
        );
    }

    #[test]
    fn variant_call_non_generic_wrong_arg_diag() {
        let diags = diags_for(
            "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(): Maybe\n  return Just(\"oops\")\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Int") && diags[0].message.contains("String"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn variant_call_non_generic_wrong_arity_diag() {
        let diags = diags_for(
            "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(): Maybe\n  return Just(1, 2)\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("expected 1") && diags[0].message.contains("found 2"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn variant_call_generic_inferred_int() {
        // `Just(1)` against expected `Maybe<Int>`: synth_ident allocates a
        // fresh Var for T, returns `Function([Var(α)], Enum(maybe, [Var(α)]))`;
        // synth_call binds α=Int via the arg check; the function's expected
        // return `Maybe<Int>` unifies cleanly.
        compile_src(
            "enum Maybe<T>\n  Just(T)\n  Nothing\nend\nfunction f(): Maybe<Int>\n  return Just(1)\nend",
        );
    }

    #[test]
    fn variant_call_generic_inferred_string_independent() {
        // Two `Just` calls in different functions get independent fresh
        // Vars: one binds T=Int, the other T=String. Without per-use-site
        // instantiation they would share a single Var and conflict.
        compile_src(
            "enum Maybe<T>\n  Just(T)\n  Nothing\nend\nfunction ints(): Maybe<Int>\n  return Just(1)\nend\nfunction strs(): Maybe<String>\n  return Just(\"hi\")\nend",
        );
    }

    #[test]
    fn variant_nullary_value_in_context() {
        // `Nothing` used as value: synth_ident retrieves the bare schema
        // `Enum(maybe, [Param(0)])`, instantiates Param→Var, returns
        // `Enum(maybe, [Var(α)])`. unify_or_diag against expected
        // `Maybe<Int>` binds α=Int.
        compile_src(
            "enum Maybe<T>\n  Just(T)\n  Nothing\nend\nfunction f(): Maybe<Int>\n  return Nothing\nend",
        );
    }

    #[test]
    fn variant_call_two_param_enum_inferred() {
        compile_src(
            "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nfunction f(): Result<Int, String>\n  return Ok(42)\nend\nfunction g(): Result<Int, String>\n  return Err(\"boom\")\nend",
        );
    }

    #[test]
    fn variant_call_generic_arg_int_to_scalar_widening() {
        // The `Int → Scalar(ZERO)` implicit-conversion gate should fire at
        // a variant-constructor arg boundary because synth_call routes
        // each arg through `check_expr` (which holds the gate).
        compile_src("enum Box<T>\n  Mk(T)\nend\nfunction f(): Box<Scalar>\n  return Mk(1)\nend");
    }

    // ----- PR-3c Task 5: generic match-pattern substitution + binding -----

    #[test]
    fn match_generic_binds_payload_type() {
        // `case Some(x) then x` against scrutinee `Maybe<Int>` must bind
        // `x: Int` (substituting Param(0) with the scrutinee's type-arg).
        // Without substitution `x` would be `Param(0)` and the body's
        // `return x` against `Int` would mismatch.
        compile_src(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): Int\n  return match m\n    case Some(x) then x\n    case Nothing then 0\n  end\nend",
        );
    }

    #[test]
    fn match_generic_payload_type_mismatch() {
        // Body returns `x: Int` but function declares `String` — exactly
        // one diagnostic for the arm-vs-seed mismatch.
        let diags = diags_for(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): String\n  return match m\n    case Some(x) then x\n    case Nothing then \"none\"\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
    }

    #[test]
    fn match_two_param_enum_binding() {
        // `case Ok(value)` binds value: Int; `case Err(_)` discards
        // String — sub-pattern wildcard is fine.
        compile_src(
            "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nfunction f(r: Result<Int, String>): Int\n  return match r\n    case Ok(value) then value\n    case Err(_) then -1\n  end\nend",
        );
    }

    #[test]
    fn match_wrong_variant_for_enum_diag() {
        // Pattern `Some` (from Maybe) on a `Result` scrutinee — the
        // variant doesn't belong to the scrutinee's enum.
        let diags = diags_for(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nenum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nfunction f(r: Result<Int, String>): Int\n  return match r\n    case Some(x) then 0\n    case Ok(v) then v\n    case Err(_) then -1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Some") || diags[0].message.contains("Maybe"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_pattern_arity_mismatch_diag() {
        // `case Some(x, y)` vs payload arity 1 — too many sub-patterns.
        // (Parser rejects `case Some()` for empty parens, and `case Some`
        // without parens parses as an Ident binding, not a nullary pattern,
        // so over-arity is the only direction expressible here.)
        let diags = diags_for(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): Int\n  return match m\n    case Some(x, y) then 0\n    case Nothing then -1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("expected 1") && diags[0].message.contains("found 2"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_nested_variant_pattern() {
        // `case Some(Some(x)) then x` — 2-level nested binding. The outer
        // substitution gives the inner pattern `Maybe<Int>`, then the
        // inner substitution binds x: Int.
        compile_src(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Maybe<Int>>): Int\n  return match m\n    case Some(Some(x)) then x\n    case Some(Nothing) then 0\n    case Nothing then -1\n  end\nend",
        );
    }

    // ----- PR-3c Task 7: match exhaustiveness -----

    #[test]
    fn match_enum_missing_variant_diag() {
        let diags = diags_for(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): Int\n  return match m\n    case Some(x) then x\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Nothing") || diags[0].message.contains("missing"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_enum_with_wildcard_passes() {
        compile_src(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): Int\n  return match m\n    case Some(x) then x\n    case _ then 0\n  end\nend",
        );
    }

    #[test]
    fn match_bool_missing_false_diag() {
        let diags = diags_for(
            "function f(b: Bool): Int\n  return match b\n    case true then 1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("false") || diags[0].message.contains("Bool"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_int_requires_wildcard_diag() {
        let diags =
            diags_for("function f(i: Int): Int\n  return match i\n    case 0 then 0\n  end\nend");
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("wildcard"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_int_with_wildcard_passes() {
        compile_src(
            "function f(i: Int): Int\n  return match i\n    case 0 then 0\n    case _ then 1\n  end\nend",
        );
    }

    #[test]
    fn match_struct_with_ident_passes() {
        compile_src(
            "struct P\n  x: Int\n  y: Int\nend\nfunction f(p: P): Int\n  return match p\n    case s then s.x\n  end\nend",
        );
    }

    #[test]
    fn match_function_value_not_matchable_diag() {
        let diags = diags_for(
            "function g(): Int\n  return 0\nend\nfunction f(): Int\n  return match g\n    case _ then 0\n  end\nend",
        );
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("function") && d.message.contains("not allowed")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn match_array_passes_with_wildcard() {
        compile_src(
            "function f(xs: Array<Int>): Int\n  return match xs\n    case _ then 0\n  end\nend",
        );
    }

    #[test]
    fn match_dict_passes_with_ident() {
        compile_src(
            "function f(d: Dict<Int, String>): Int\n  return match d\n    case s then 0\n  end\nend",
        );
    }

    #[test]
    fn match_two_param_enum_missing_variant_diag() {
        // Use a user-defined `MyResult` since the in-crate test helpers
        // bypass `compile()`'s built-ins loading. Behavior equivalence:
        // built-in Result is just an enum with the same shape.
        let diags = diags_for(
            "enum MyResult<T, E>\n  Ok(T)\n  Err(E)\nend\nfunction f(r: MyResult<Int, String>): Int\n  return match r\n    case Ok(v) then v\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Err"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_nested_payload_missing_inner_variant_diag() {
        // User-defined `Maybe<T>` (same shape as built-in Option). Outer
        // Some/Nothing covered; inner Maybe's `Nothing` is missing at
        // the `Some(...)` column.
        let diags = diags_for(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(oo: Maybe<Maybe<Int>>): Int\n  return match oo\n    case Some(Some(x)) then x\n    case Nothing then -1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Nothing") || diags[0].message.contains("missing"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_nested_payload_complete_passes() {
        compile_src(
            "enum Maybe<T>\n  Some(T)\n  Nothing\nend\nfunction f(oo: Maybe<Maybe<Int>>): Int\n  return match oo\n    case Some(Some(x)) then x\n    case Some(Nothing) then 0\n    case Nothing then -1\n  end\nend",
        );
    }

    // Exhaustiveness coverage gaps surfaced by code-quality review:
    // pin String require_catchall behavior + the no-cascade skip path
    // for scrutinees whose type is `Ty::Error` (an upstream diag was
    // already pinned and exhaust must not pile on). Scalar's
    // require_catchall path is structurally identical to Int's
    // (`match_int_requires_wildcard_diag`); a dedicated Scalar test
    // can't be written because float-literal patterns are rejected
    // at parse phase before exhaust runs.

    #[test]
    fn match_string_requires_wildcard_diag() {
        let diags = diags_for(
            "function f(s: String): Int\n  return match s\n    case \"hi\" then 1\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("wildcard"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn match_string_with_wildcard_passes() {
        compile_src(
            "function f(s: String): Int\n  return match s\n    case \"hi\" then 1\n    case _ then 0\n  end\nend",
        );
    }

    #[test]
    fn match_error_scrutinee_skips_exhaustiveness() {
        // The scrutinee references an undefined name → its synthesized
        // type is `Ty::Error`. exhaust must skip (no-cascade) so the
        // single "undefined name" diag isn't joined by a spurious
        // "non-exhaustive" diag.
        let diags = diags_for(
            "function f(): Int\n  return match undefined_var\n    case _ then 0\n  end\nend",
        );
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("undefined_var"),
            "msg: {}",
            diags[0].message
        );
    }
}
