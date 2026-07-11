//! Call, identifier, and variant-constructor checking.
//!
//! Split out of `check.rs` in the 2026-07 sema refactor. Owns `Call`
//! checking (both directions), identifier resolution to a type, and enum
//! variant-constructor typing and instantiation — the insertion point for
//! PR-3f's variadic `printf` and `kahan_sum` special forms. Methods run on
//! `TypeChecker` (defined in the parent `check` module); the driver-
//! dispatched ones are `pub(super)`.

use super::TypeChecker;
use crate::ast::Expr;
use crate::ids::DefId;
use crate::sema::resolve::DefKind;
use crate::sema::ty::Ty;
use crate::source::Span;

impl TypeChecker<'_> {
    /// Bidirectional check for `Call` expressions. Mirrors `synth_call`'s
    /// arity / arg-type / not-callable diagnostics, but pre-unifies the
    /// callee's return type with the outer `expected` so type-Vars in the
    /// signature pick up outer constraints before per-arg checking.
    pub(super) fn check_call(
        &mut self,
        e: &Expr,
        callee: &Expr,
        args: &[Expr],
        expected: &Ty,
    ) -> Ty {
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
                self.diagnostics.push(crate::sema::diag::not_callable(
                    self.definitions,
                    callee.span,
                    &other,
                ));
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

    pub(super) fn synth_ident(&mut self, e: &Expr) -> Ty {
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

    /// Function call: synth callee, expect `Ty::Function(param_tys, ret)`,
    /// check each argument against its declared param type, return `ret`.
    /// Non-function callees emit `not_callable`; arity mismatches emit
    /// `wrong_arity`. In both error cases we skip per-argument checking so
    /// downstream diagnostics don't cascade.
    pub(super) fn synth_call(&mut self, callee: &Expr, args: &[Expr], call_span: Span) -> Ty {
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
                self.diagnostics.push(crate::sema::diag::not_callable(
                    self.definitions,
                    callee.span,
                    &other,
                ));
                Ty::Error
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::sema::check::test_support::{compile_src, diags_for};

    #[test]
    fn ident_resolves_to_param_type() {
        compile_src("function f(x: Int): Int\n  return x\nend");
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
}
