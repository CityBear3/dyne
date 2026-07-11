//! Match and pattern checking.
//!
//! Split out of `check.rs` in the 2026-07 sema refactor. Owns `match`
//! synthesis, per-arm body unification, and pattern checking (including
//! generic-payload substitution) — the type-side counterpart to
//! `exhaust.rs`. `synth_match` runs on `TypeChecker` (parent `check`
//! module) as `pub(super)` so the driver can dispatch to it; the arm and
//! pattern helpers are private to this module.

use super::TypeChecker;
use crate::ast::{Expr, MatchArm, Pattern, PatternKind};
use crate::sema::ty::Ty;

impl TypeChecker<'_> {
    pub(super) fn synth_match(&mut self, scrutinee: &Expr, arms: &[MatchArm]) -> Ty {
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
                                self.definitions,
                                p.span,
                                other,
                                "enum",
                            ));
                        return;
                    }
                };
                if variant_info.parent_enum != parent {
                    self.diagnostics
                        .push(crate::sema::diag::wrong_variant_for_enum(
                            self.definitions,
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
}

#[cfg(test)]
mod tests {
    use crate::sema::check::test_support::{compile_src, diags_for};

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
