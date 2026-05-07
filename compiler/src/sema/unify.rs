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

    /// Unify two types. On failure, returns `Err((a, b))` with the
    /// conflicting (resolved) types. `Ty::Error` unifies with anything to
    /// preserve the no-cascade invariant downstream.
    #[allow(dead_code)] // Wired by PR-3c's enum constructor inference.
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
            // infinite-loop. Latent in 3b (concrete-only) but PR-3c will
            // hit this when the same scrutinee var unifies twice.
            (Ty::Var(v), Ty::Var(w)) if v == w => Ok(()),
            (Ty::Var(v), other) | (other, Ty::Var(v)) => {
                self.cells[v.0 as usize] = Some(other);
                Ok(())
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
