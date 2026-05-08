//! Unification table for type variables.
//!
//! PR-3b uses this for match-arm unification (each arm's body type must
//! unify with the seed type from the first arm). PR-3c will add enum
//! constructor inference.
//!
//! The implementation is a `Vec<Option<Ty>>` indexed by `TypeVarId`.
//! Path compression / union-by-rank is deferred — profiling can drive it
//! if unification ever becomes a bottleneck.

use crate::sema::ty::{Ty, TypeVarId};

pub(crate) struct Table {
    cells: Vec<Option<Ty>>,
}

impl Table {
    pub(crate) fn new() -> Self {
        Self { cells: Vec::new() }
    }

    #[allow(dead_code)] // Wired by PR-3c's enum constructor inference.
    pub(crate) fn fresh(&mut self) -> TypeVarId {
        let id = TypeVarId(self.cells.len() as u32);
        self.cells.push(None);
        id
    }

    /// Resolve `Var(α)` chains until a non-Var or unsolved Var is hit.
    pub(crate) fn resolve(&self, ty: &Ty) -> Ty {
        let mut cur = ty.clone();
        loop {
            match &cur {
                Ty::Var(v) => match &self.cells[v.0 as usize] {
                    Some(t) => cur = t.clone(),
                    None => return cur,
                },
                _ => return cur,
            }
        }
    }

    /// Recursive variant of [`Self::resolve`]: also rewrites `Var`s nested
    /// inside compound types (`Function` / `Enum` / `Array` / `Dict`).
    ///
    /// Plain `resolve` only walks the outermost Var chain — when the
    /// outer head is already concrete (e.g. `Enum(option, [Var(α)])`),
    /// any unification-bound Var sitting inside a child position is left
    /// alone. PR-3c's exhaustiveness check needs the deeper rewrite:
    /// when the scrutinee is constructed inline (`Some(Some(1))`), the
    /// outer Option's argument is still a Var when `synth_match` runs,
    /// and the inner column's substituted payload type would otherwise
    /// fall into exhaust's `Ty::Var(_)` skip arm.
    ///
    /// Scope: resolves only the exhaust-level gap. Storage of unresolved
    /// Vars inside `TypedProgram.types` (the §1078 leak) is a separate
    /// concern handled later — this helper exists to keep the synth_match
    /// fix minimal and not perturb other expression types.
    ///
    /// `Vec`/`Mat`/`Scalar` carry no `Ty` children (their type
    /// parameters are size and dimension data), so they pass through
    /// unchanged via the head clone.
    pub(crate) fn resolve_deep(&self, ty: &Ty) -> Ty {
        let head = self.resolve(ty);
        match head {
            Ty::Function(args, ret) => Ty::Function(
                args.iter().map(|a| self.resolve_deep(a)).collect(),
                Box::new(self.resolve_deep(&ret)),
            ),
            Ty::Enum(def, args) => {
                Ty::Enum(def, args.iter().map(|a| self.resolve_deep(a)).collect())
            }
            Ty::Array(t) => Ty::Array(Box::new(self.resolve_deep(&t))),
            Ty::Dict(k, v) => Ty::Dict(
                Box::new(self.resolve_deep(&k)),
                Box::new(self.resolve_deep(&v)),
            ),
            other => other,
        }
    }

    /// Unify two types structurally. On failure, returns `Err((a, b))`
    /// with the conflicting (resolved) types — the innermost (deepest)
    /// mismatch encountered via short-circuit `?` propagation through
    /// compound arms. `Ty::Error` unifies with anything to preserve the
    /// no-cascade invariant downstream.
    ///
    /// Compound types (`Function`, `Enum`, `Array`, `Dict`) recurse: their
    /// children unify pairwise. Without recursion, a nested `Ty::Var` (e.g.
    /// `Enum(maybe, [Var(α)])` vs `Enum(maybe, [Int])`) would never get
    /// bound because outer-only equality fails. PR-3c's variant-constructor
    /// inference relies on this — `Just(1)`'s synthesized
    /// `Function([Var(α)], Enum(maybe, [Var(α)]))` needs the arg-Var to
    /// pick up `Int` from the per-arg `check_expr`, then the function-
    /// return unification picks up `Maybe<Int>` cleanly.
    ///
    /// No occurs-check: dyne has no recursive type aliases, and Enums/
    /// Structs reference DefIds (not nested Tys), so no Ty cycles can
    /// form by construction.
    // Invariant: bindings written by successful sub-unifications (Var-
    // arms, recursion through compound arms) PERSIST in the table even
    // when a later sibling fails and `?` bubbles Err. This is currently
    // safe because Var allocation is per-call-site
    // (`instantiate_variant_schema` mints a fresh batch per use site),
    // so a stale partial binding from a failed unify cannot collide
    // with a future unrelated unify. See
    // `unify_compound_partial_bind_persists_after_err` for a regression
    // test pinning this behavior.
    pub(crate) fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), (Ty, Ty)> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (a, b) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),
            // Param is a schema-only sentinel (variant signatures). Use
            // sites substitute Param → fresh Var via `synth_ident` (Task 4)
            // before unification can see them. If a Param ever reaches
            // unify, the substitution is buggy — fail fast rather than
            // silently treat `Param(0)` as unifiable with `Param(0)` from a
            // different schema instantiation.
            //
            // This arm sits immediately after the Error arm so it pre-empts
            // the Var-binding arm below: otherwise `unify(Var(α), Param(0))`
            // would silently bind `cells[α] = Param(0)`, polluting the
            // unification table with a schema sentinel and surfacing the
            // bug later as a `<param #0>` diagnostic instead of at the
            // buggy substitution site.
            (a @ Ty::Param(_), b) | (a, b @ Ty::Param(_)) => Err((a, b)),
            // Identical-var early-out: without this, the next arm would
            // bind `cells[v] = Some(Var(v))`, which makes `resolve()`
            // infinite-loop. Latent in 3b (concrete-only) but PR-3c hits
            // this when the same scrutinee var unifies twice.
            (Ty::Var(v), Ty::Var(w)) if v == w => Ok(()),
            (Ty::Var(v), other) | (other, Ty::Var(v)) => {
                self.cells[v.0 as usize] = Some(other);
                Ok(())
            }
            (Ty::Function(args_a, ret_a), Ty::Function(args_b, ret_b))
                if args_a.len() == args_b.len() =>
            {
                for (l, r) in args_a.iter().zip(args_b.iter()) {
                    self.unify(l, r)?;
                }
                self.unify(&ret_a, &ret_b)
            }
            (Ty::Enum(da, args_a), Ty::Enum(db, args_b))
                if da == db && args_a.len() == args_b.len() =>
            {
                for (l, r) in args_a.iter().zip(args_b.iter()) {
                    self.unify(l, r)?;
                }
                Ok(())
            }
            (Ty::Array(t_a), Ty::Array(t_b)) => self.unify(&t_a, &t_b),
            (Ty::Dict(k_a, v_a), Ty::Dict(k_b, v_b)) => {
                self.unify(&k_a, &k_b)?;
                self.unify(&v_a, &v_b)
            }
            (a, b) if a == b => Ok(()),
            (a, b) => Err((a, b)),
        }
    }

    /// Walk to a concrete type. Returns `Err(v)` if `ty` resolves to an
    /// unsolved variable — the caller should then emit an
    /// `unresolved_type_var` diagnostic.
    #[allow(dead_code)] // Wired by PR-3c's enum constructor inference.
    pub(crate) fn assert_resolved(&self, ty: &Ty) -> Result<Ty, TypeVarId> {
        match self.resolve(ty) {
            Ty::Var(v) => Err(v),
            other => Ok(other),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_returns_distinct_ids() {
        let mut t = Table::new();
        assert_ne!(t.fresh(), t.fresh());
    }

    #[test]
    fn unify_var_with_concrete_resolves() {
        let mut t = Table::new();
        let v = t.fresh();
        t.unify(&Ty::Var(v), &Ty::Int).unwrap();
        assert_eq!(t.resolve(&Ty::Var(v)), Ty::Int);
    }

    #[test]
    fn unify_two_vars_chains() {
        let mut t = Table::new();
        let a = t.fresh();
        let b = t.fresh();
        t.unify(&Ty::Var(a), &Ty::Var(b)).unwrap();
        t.unify(&Ty::Var(b), &Ty::Bool).unwrap();
        assert_eq!(t.resolve(&Ty::Var(a)), Ty::Bool);
    }

    #[test]
    fn unify_concrete_mismatch_errors() {
        let mut t = Table::new();
        assert!(t.unify(&Ty::Int, &Ty::Bool).is_err());
    }

    #[test]
    fn unify_error_with_anything_succeeds() {
        let mut t = Table::new();
        t.unify(&Ty::Error, &Ty::Int).unwrap();
        t.unify(&Ty::Int, &Ty::Error).unwrap();
    }

    #[test]
    fn unify_var_with_itself_is_no_op() {
        // Regression for the self-loop bug: without the v == w early-out,
        // unify(Var(α), Var(α)) would write cells[α] = Some(Var(α)) and
        // resolve() would infinite-loop. After the fix, resolve still
        // returns the unsolved var.
        let mut t = Table::new();
        let v = t.fresh();
        t.unify(&Ty::Var(v), &Ty::Var(v)).unwrap();
        assert_eq!(t.resolve(&Ty::Var(v)), Ty::Var(v));
    }

    #[test]
    fn unify_compound_partial_bind_persists_after_err() {
        // Partial-binding pollution after a failed compound unify is
        // intentional but undocumented before this commit. Recursion
        // through compound arms uses `?` propagation: a Var binding
        // written by an early successful sub-unify is NOT rolled back
        // when a later sibling fails. This regression test pins the
        // current behavior.
        //
        // Setup:
        //   unify(Function([Var(α), Int], Bool),
        //         Function([Int,    String], Bool))
        //     - First arg pair:  (Var(α), Int)    → cells[α] = Int (Ok)
        //     - Second arg pair: (Int,    String) → fails → ? bubbles Err
        // The α=Int binding from the first pair persists in the table
        // even though the overall unify returned Err.
        //
        // Currently safe because each variant-constructor use site
        // mints its own fresh Var batch via
        // `instantiate_variant_schema`, so a stale binding from a
        // failed unify cannot collide with an unrelated future unify.
        // If that freshness invariant is ever weakened, this test
        // surfaces the change as a deliberate failure here rather than
        // as a hard-to-trace cross-call-site type-mismatch.
        let mut t = Table::new();
        let alpha = t.fresh();
        let res = t.unify(
            &Ty::Function(vec![Ty::Var(alpha), Ty::Int], Box::new(Ty::Bool)),
            &Ty::Function(vec![Ty::Int, Ty::String], Box::new(Ty::Bool)),
        );
        assert!(
            res.is_err(),
            "expected unify to fail on the (Int, String) sub-pair"
        );
        assert_eq!(
            t.resolve(&Ty::Var(alpha)),
            Ty::Int,
            "partial binding from the first arg pair must persist after Err"
        );
    }

    #[test]
    fn unify_var_with_param_errors_without_polluting_table() {
        // Regression for the arm-ordering bug: if the Param fail-fast arm
        // were placed AFTER the Var-binding arm, `unify(Var(α), Param(0))`
        // would silently bind `cells[α] = Param(0)`, polluting the table
        // with a schema sentinel. The arm now sits before the Var arm so
        // both directions error out and α stays unbound.
        let mut t = Table::new();
        let v = t.fresh();
        assert!(t.unify(&Ty::Var(v), &Ty::Param(0)).is_err());
        assert_eq!(t.resolve(&Ty::Var(v)), Ty::Var(v));
        let w = t.fresh();
        assert!(t.unify(&Ty::Param(0), &Ty::Var(w)).is_err());
        assert_eq!(t.resolve(&Ty::Var(w)), Ty::Var(w));
    }
}
