//! Dimension vectors, the SI unit registry, and unit-expression evaluation.
//!
//! Extracted from `ty.rs` in the 2026-07 sema refactor. This module owns
//! everything about *units*: the 7-element SI exponent vector, overflow-
//! checked dimension arithmetic, the base + derived unit name registry,
//! and `eval_unit_expr` (AST `UnitExpr` → `Dimension`).

use crate::diag::Diagnostic;

/// Integer dimension vector over the seven SI base dimensions, indexed
/// parallel to [`BASE_NAMES`]: `[m, kg, s, A, K, mol, cd]`.
///
/// PR-3b only uses `Dimension::ZERO` (dimensionless). PR-3d populates
/// the inner `i8` array via `mul`/`div`/`pow` arithmetic and the
/// `UnitRegistry` lookup table; `format_si` renders the canonical SI
/// base form for diagnostics.
///
/// The inner array is `pub(crate)` — accessible to crate-internal
/// callers (`UnitRegistry::lookup`, sema tests) but NOT exposed in the
/// external `dyne::sema::ty` API surface. Future migration to rational
/// exponents (PR-3? — noise spectroscopy use cases) stays scoped to
/// the crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dimension(pub(crate) [i8; 7]);

/// Single source of truth for the SI base-dimension order: each index
/// corresponds to position `i` of [`Dimension`]'s inner array. All other
/// modules (the registry, format_si, doc-comments) reference this name
/// rather than restating the order.
const BASE_NAMES: [&str; 7] = ["m", "kg", "s", "A", "K", "mol", "cd"];

impl Dimension {
    pub const ZERO: Self = Self([0; 7]);

    /// Returns true iff this dimension is the dimensionless `ZERO`.
    pub fn is_dimensionless(self) -> bool {
        self == Self::ZERO
    }

    /// Renders the canonical SI base form as ASCII. Examples:
    ///   ZERO              → "1"
    ///   [1, 0, ...]       → "m"
    ///   [1, 1, -2, ...]   → "m*kg*s^-2"
    /// Negative exponents render as `name^-n`. Exponent of 1 elides.
    /// Order follows [`BASE_NAMES`].
    pub fn format_si(self) -> String {
        if self.is_dimensionless() {
            return "1".to_string();
        }
        // At most 7 components — preallocate to avoid reallocation as
        // each non-zero exponent pushes its rendered factor.
        let mut parts = Vec::with_capacity(BASE_NAMES.len());
        for (&exp, name) in self.0.iter().zip(BASE_NAMES.iter()) {
            if exp == 0 {
                continue;
            }
            if exp == 1 {
                parts.push((*name).to_string());
            } else {
                parts.push(format!("{name}^{exp}"));
            }
        }
        parts.join("*")
    }
}

impl std::fmt::Display for Dimension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.format_si())
    }
}

/// Reported by `Dimension::mul` / `div` / `pow` when an i8 element would
/// overflow during the operation. Sites that compute dimensions push
/// `dimension_overflow` diagnostics and produce `Ty::Error` to suppress
/// cascade (Q9 migration; `dim_op_result` maps the overflow to `None`,
/// which callers turn into `Ty::Error`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverflowError;

// `mul` / `div` are unit-algebra operations on exponent vectors —
// `kg * m/s = kg·m/s` is pointwise addition of exponents, not the
// numeric `std::ops::Mul`. The names match the domain meaning, hence
// the family-wide `should_implement_trait` allow.
#[allow(clippy::should_implement_trait)]
impl Dimension {
    /// Pointwise add: each element of `self` is paired with the
    /// corresponding element of `other` and summed with checked i8
    /// arithmetic. Returns `Err(OverflowError)` if any element
    /// overflows i8 (`i8::MIN..=i8::MAX`).
    pub fn mul(self, other: Self) -> Result<Self, OverflowError> {
        self.pointwise(other, i8::checked_add)
    }

    /// Pointwise subtract: each element of `self` is paired with the
    /// corresponding element of `other` and subtracted with checked i8
    /// arithmetic. Returns `Err(OverflowError)` if any element
    /// underflows i8.
    pub fn div(self, other: Self) -> Result<Self, OverflowError> {
        self.pointwise(other, i8::checked_sub)
    }

    /// Pointwise multiply by integer exponent. `pow(self, n)` produces a
    /// dimension where each element is `self[i] * n`. Returns Err on i8
    /// overflow.
    pub fn pow(self, n: i8) -> Result<Self, OverflowError> {
        let mut out = [0i8; 7];
        for (dst, &a) in out.iter_mut().zip(&self.0) {
            *dst = a.checked_mul(n).ok_or(OverflowError)?;
        }
        Ok(Self(out))
    }

    fn pointwise(self, other: Self, op: fn(i8, i8) -> Option<i8>) -> Result<Self, OverflowError> {
        let mut out = [0i8; 7];
        for (dst, (&a, &b)) in out.iter_mut().zip(self.0.iter().zip(&other.0)) {
            *dst = op(a, b).ok_or(OverflowError)?;
        }
        Ok(Self(out))
    }
}

/// Static built-in unit registry. Maps unit names to canonical
/// `Dimension` values. Per /design-discussion 2026-05-08 Q3, scope is
/// SI base 7 + 8 derived units. SI prefixes (km, ms, μs), CGS (cm, g),
/// and scale-factor folding are deferred to PR-3e or later.
pub(crate) struct UnitRegistry;

impl UnitRegistry {
    /// Look up a unit name. Returns `Some(dim)` for known units,
    /// `None` for unknown — caller emits `unknown_unit` diagnostic.
    pub(crate) fn lookup(name: &str) -> Option<Dimension> {
        match name {
            // SI base units
            "m" => Some(Dimension([1, 0, 0, 0, 0, 0, 0])),
            "kg" => Some(Dimension([0, 1, 0, 0, 0, 0, 0])),
            "s" => Some(Dimension([0, 0, 1, 0, 0, 0, 0])),
            "A" => Some(Dimension([0, 0, 0, 1, 0, 0, 0])),
            "K" => Some(Dimension([0, 0, 0, 0, 1, 0, 0])),
            "mol" => Some(Dimension([0, 0, 0, 0, 0, 1, 0])),
            "cd" => Some(Dimension([0, 0, 0, 0, 0, 0, 1])),
            // SI derived units (in canonical base form)
            "N" => Some(Dimension([1, 1, -2, 0, 0, 0, 0])), // kg*m/s^2
            "J" => Some(Dimension([2, 1, -2, 0, 0, 0, 0])), // N*m = kg*m^2/s^2
            "W" => Some(Dimension([2, 1, -3, 0, 0, 0, 0])), // J/s
            "Pa" => Some(Dimension([-1, 1, -2, 0, 0, 0, 0])), // N/m^2
            "Hz" => Some(Dimension([0, 0, -1, 0, 0, 0, 0])), // 1/s
            "C" => Some(Dimension([0, 0, 1, 1, 0, 0, 0])),  // A*s
            "V" => Some(Dimension([2, 1, -3, -1, 0, 0, 0])), // W/A = kg*m^2/(s^3*A)
            // Ω: the `byte 0xCE` lexer rejects this Unicode char, so the
            // arm is unreachable from source today. Kept for completeness
            // so the registry covers the full 8-derived set; lexer
            // Unicode support arrives with the SI prefix / CGS work
            // (PR-3e or later).
            "Ω" => Some(Dimension([2, 1, -3, -2, 0, 0, 0])), // V/A
            _ => None,
        }
    }
}

/// Evaluate a `UnitExpr` AST node to a `Dimension` value. Recursively
/// walks Atom / Mul / Div / Pow nodes. Emits diagnostics on unknown
/// unit names, exponents outside i8 range, and dimension-component
/// overflow. Returns `Err(())` on any error (the diagnostic is already
/// pushed at the failure site, so the unit error type carries no payload);
/// callers (`lower_scalar` / `lower_vec`) translate this into `Ty::Error`,
/// which `synth_arith` / `synth_pow` short-circuit without further diags.
///
/// Q9 (CQ M4 from PR-3d-α /review): α returned `Dimension::ZERO` as a
/// cascade-suppression sentinel here, but a `Scalar(ZERO)` from a *failed*
/// lowering is indistinguishable from a genuinely dimensionless `Scalar`.
/// Once β's `synth_arith` flips to `if d1 != d2 then dimension_mismatch`,
/// that ambiguity would suppress root-cause diags and emit misleading
/// double-diags. Propagating `Err(())` → `Ty::Error` removes the sentinel.
///
/// `Mul` / `Div` evaluate *both* operands before propagating an error so
/// every distinct unknown unit in a compound annotation (e.g.
/// `foo*bar/foo`) is still reported in one pass — short-circuiting on the
/// first failure would drop sibling diagnostics.
///
/// Unknown-unit diagnostics are deduplicated by message against the
/// already-emitted `diags` vec so a typo like `xyz` reported in the
/// same diagnostic pile (e.g. multiple params in one signature, or
/// a compound `xyz*xyz/xyz` in one annotation) surfaces once. Dedup
/// uses the rendered message so it stays scoped to the same `&mut
/// Vec<Diagnostic>` — across separate vecs (signature_pass vs
/// TypeChecker.diagnostics, merged at the end of `check()`) the
/// dedup does not cross the boundary; a follow-up can hoist a shared
/// `HashSet<String>` if that edge case surfaces.
pub(crate) fn eval_unit_expr(
    u: &crate::ast::UnitExpr,
    diags: &mut Vec<Diagnostic>,
) -> Result<Dimension, ()> {
    use crate::ast::UnitExprKind;
    use crate::sema::diag;
    match &u.kind {
        UnitExprKind::Atom(name) => match UnitRegistry::lookup(name) {
            Some(dim) => Ok(dim),
            None => {
                let new_diag = diag::unknown_unit(u.span, name);
                // O(n) scan over already-emitted diags. Realistic compile
                // produces O(10) diags total, so the scan is negligible
                // compared to allocation. If diag piles ever grow large
                // (e.g. tens of thousands of unit annotations in one
                // module), hoist a `HashSet<String>` to `check()` and
                // thread it through `lower_type` / `eval_unit_expr` for
                // O(1) lookup; that refactor is intentionally deferred.
                if !diags.iter().any(|d| d.message == new_diag.message) {
                    diags.push(new_diag);
                }
                Err(())
            }
        },
        UnitExprKind::Mul(a, b) => {
            // Evaluate both sides first so every unknown atom is reported,
            // then propagate any failure (`?` short-circuits only after
            // both diags are collected).
            let l = eval_unit_expr(a, diags);
            let r = eval_unit_expr(b, diags);
            l?.mul(r?).map_err(|_| {
                diags.push(diag::dimension_overflow(u.span));
            })
        }
        UnitExprKind::Div(a, b) => {
            let l = eval_unit_expr(a, diags);
            let r = eval_unit_expr(b, diags);
            l?.div(r?).map_err(|_| {
                diags.push(diag::dimension_overflow(u.span));
            })
        }
        UnitExprKind::Pow(base, n) => {
            // Parser produces i64; narrow to i8 with `try_from` rather than
            // a manual MIN/MAX comparison so the conversion intent is
            // explicit and matches Effective Rust Item 5.
            let Ok(exp) = i8::try_from(*n) else {
                diags.push(diag::unit_exponent_out_of_range(u.span, *n));
                return Err(());
            };
            let base_dim = eval_unit_expr(base, diags)?;
            base_dim.pow(exp).map_err(|_| {
                diags.push(diag::dimension_overflow(u.span));
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimension_mul_pointwise_adds_elements() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        let m_per_s = Dimension([1, 0, -1, 0, 0, 0, 0]);
        // kg * m/s = kg*m/s = [1, 1, -1, 0, 0, 0, 0]
        let result = kg.mul(m_per_s).unwrap();
        assert_eq!(result, Dimension([1, 1, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_mul_overflow_returns_err() {
        let big = Dimension([100, 0, 0, 0, 0, 0, 0]);
        let bigger = Dimension([50, 0, 0, 0, 0, 0, 0]);
        // 100 + 50 = 150, overflows i8 (max 127).
        assert_eq!(big.mul(bigger), Err(OverflowError));
    }

    #[test]
    fn dimension_div_pointwise_subtracts_elements() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        let s = Dimension([0, 0, 1, 0, 0, 0, 0]);
        // m / s = [1, 0, -1, 0, 0, 0, 0]
        let result = m.div(s).unwrap();
        assert_eq!(result, Dimension([1, 0, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_div_underflow_returns_err() {
        let small = Dimension([-100, 0, 0, 0, 0, 0, 0]);
        let big_pos = Dimension([50, 0, 0, 0, 0, 0, 0]);
        // -100 - 50 = -150, underflows i8 (min -128).
        assert_eq!(small.div(big_pos), Err(OverflowError));
    }

    #[test]
    fn dimension_pow_multiplies_elements_by_exponent() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        // m ^ 3 = m^3 = [3, 0, 0, 0, 0, 0, 0]
        let result = m.pow(3).unwrap();
        assert_eq!(result, Dimension([3, 0, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_pow_overflow_returns_err() {
        let m_strong = Dimension([10, 0, 0, 0, 0, 0, 0]);
        // 10 * 50 = 500, overflows i8.
        assert_eq!(m_strong.pow(50), Err(OverflowError));
    }

    #[test]
    fn dimension_pow_zero_yields_dimensionless() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(kg.pow(0).unwrap(), Dimension::ZERO);
    }

    #[test]
    fn dimension_pow_negative_works() {
        let s = Dimension([0, 0, 1, 0, 0, 0, 0]);
        // s ^ -2 = [0, 0, -2, 0, 0, 0, 0] (e.g. acceleration unit denominator)
        assert_eq!(s.pow(-2).unwrap(), Dimension([0, 0, -2, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_pow_at_i8_max_boundary_succeeds() {
        // 1 * 127 = 127 — exactly i8::MAX, no overflow.
        let unit = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(unit.pow(127).unwrap(), Dimension([127, 0, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_pow_overflows_just_above_max() {
        // 2 * 127 = 254 — overflows i8::MAX (127).
        let two = Dimension([2, 0, 0, 0, 0, 0, 0]);
        assert_eq!(two.pow(127), Err(OverflowError));
    }

    #[test]
    fn dimension_pow_at_i8_min_boundary_succeeds() {
        // 1 * -128 = -128 — exactly i8::MIN, no underflow.
        let unit = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(unit.pow(-128).unwrap(), Dimension([-128, 0, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_pow_underflows_just_below_min() {
        // 2 * -128 = -256 — underflows i8::MIN (-128).
        let two = Dimension([2, 0, 0, 0, 0, 0, 0]);
        assert_eq!(two.pow(-128), Err(OverflowError));
    }

    // `mul` is pointwise checked_add; `div` is pointwise checked_sub.
    // Boundary tests parallel to `dimension_pow_at_i8_*` above.

    #[test]
    fn dimension_mul_at_i8_max_boundary_succeeds() {
        // 127 + 0 = 127 — exactly i8::MAX.
        let a = Dimension([127, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.mul(Dimension::ZERO).unwrap(), a);
    }

    #[test]
    fn dimension_mul_overflows_just_above_max() {
        // 127 + 1 = 128 — overflows i8::MAX.
        let a = Dimension([127, 0, 0, 0, 0, 0, 0]);
        let b = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.mul(b), Err(OverflowError));
    }

    #[test]
    fn dimension_mul_at_i8_min_boundary_succeeds() {
        // -128 + 0 = -128 — exactly i8::MIN.
        let a = Dimension([-128, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.mul(Dimension::ZERO).unwrap(), a);
    }

    #[test]
    fn dimension_mul_underflows_just_below_min() {
        // -128 + -1 = -129 — underflows i8::MIN.
        let a = Dimension([-128, 0, 0, 0, 0, 0, 0]);
        let b = Dimension([-1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.mul(b), Err(OverflowError));
    }

    #[test]
    fn dimension_div_at_i8_max_boundary_succeeds() {
        // 127 - 0 = 127 — exactly i8::MAX.
        let a = Dimension([127, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.div(Dimension::ZERO).unwrap(), a);
    }

    #[test]
    fn dimension_div_overflows_just_above_max() {
        // 127 - (-1) = 128 — overflows i8::MAX.
        let a = Dimension([127, 0, 0, 0, 0, 0, 0]);
        let b = Dimension([-1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.div(b), Err(OverflowError));
    }

    #[test]
    fn dimension_div_at_i8_min_boundary_succeeds() {
        // -128 - 0 = -128 — exactly i8::MIN.
        let a = Dimension([-128, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.div(Dimension::ZERO).unwrap(), a);
    }

    #[test]
    fn dimension_div_underflows_just_below_min() {
        // -128 - 1 = -129 — underflows i8::MIN.
        let a = Dimension([-128, 0, 0, 0, 0, 0, 0]);
        let b = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.div(b), Err(OverflowError));
    }

    #[test]
    fn format_si_dimensionless_is_one() {
        assert_eq!(Dimension::ZERO.format_si(), "1");
    }

    #[test]
    fn format_si_single_base_unit_no_exponent() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(m.format_si(), "m");
    }

    #[test]
    fn format_si_kg_no_exponent() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(kg.format_si(), "kg");
    }

    #[test]
    fn format_si_negative_exponent() {
        let inv_s = Dimension([0, 0, -1, 0, 0, 0, 0]);
        assert_eq!(inv_s.format_si(), "s^-1");
    }

    #[test]
    fn format_si_multi_component_force_in_base_form() {
        // N = kg*m*s^-2 = [1, 1, -2, 0, 0, 0, 0]
        let newton_base = Dimension([1, 1, -2, 0, 0, 0, 0]);
        assert_eq!(newton_base.format_si(), "m*kg*s^-2");
    }

    #[test]
    fn format_si_higher_positive_exponent() {
        // m^3 (volume) = [3, 0, 0, 0, 0, 0, 0]
        let cubic_m = Dimension([3, 0, 0, 0, 0, 0, 0]);
        assert_eq!(cubic_m.format_si(), "m^3");
    }

    #[test]
    fn format_si_skips_zero_exponents() {
        // m^2 / s = [2, 0, -1, 0, 0, 0, 0] — kg, A, K, mol, cd zero exponents skipped.
        let acc_like = Dimension([2, 0, -1, 0, 0, 0, 0]);
        assert_eq!(acc_like.format_si(), "m^2*s^-1");
    }

    #[test]
    fn format_si_renders_all_base_names() {
        // Every base exponent = 1 — pins the BASE_NAMES order plus
        // confirms all 7 base names render. Covers the order the unit
        // algebra walks (m, kg, s, A, K, mol, cd) in one assertion so
        // a typo in BASE_NAMES surfaces immediately.
        let all_ones = Dimension([1, 1, 1, 1, 1, 1, 1]);
        assert_eq!(all_ones.format_si(), "m*kg*s*A*K*mol*cd");
    }

    #[test]
    fn dimension_display_delegates_to_format_si() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(format!("{}", kg), "kg");
        assert_eq!(format!("{}", Dimension::ZERO), "1");
    }

    #[test]
    fn unit_registry_si_base_seven() {
        assert_eq!(
            UnitRegistry::lookup("m"),
            Some(Dimension([1, 0, 0, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("kg"),
            Some(Dimension([0, 1, 0, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("s"),
            Some(Dimension([0, 0, 1, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("A"),
            Some(Dimension([0, 0, 0, 1, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("K"),
            Some(Dimension([0, 0, 0, 0, 1, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("mol"),
            Some(Dimension([0, 0, 0, 0, 0, 1, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("cd"),
            Some(Dimension([0, 0, 0, 0, 0, 0, 1]))
        );
    }

    #[test]
    fn unit_registry_derived_newton() {
        // N = kg*m/s^2 = [1, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("N"),
            Some(Dimension([1, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_joule() {
        // J = N*m = kg*m^2/s^2 = [2, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("J"),
            Some(Dimension([2, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_watt() {
        // W = J/s = kg*m^2/s^3 = [2, 1, -3, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("W"),
            Some(Dimension([2, 1, -3, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_pascal() {
        // Pa = N/m^2 = kg/(m*s^2) = [-1, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Pa"),
            Some(Dimension([-1, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_hertz() {
        // Hz = 1/s = [0, 0, -1, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Hz"),
            Some(Dimension([0, 0, -1, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_coulomb() {
        // C = A*s = [0, 0, 1, 1, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("C"),
            Some(Dimension([0, 0, 1, 1, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_volt() {
        // V = W/A = kg*m^2/(s^3*A) = [2, 1, -3, -1, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("V"),
            Some(Dimension([2, 1, -3, -1, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_ohm() {
        // Ω = V/A = kg*m^2/(s^3*A^2) = [2, 1, -3, -2, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Ω"),
            Some(Dimension([2, 1, -3, -2, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_unknown_returns_none() {
        assert_eq!(UnitRegistry::lookup("unknown_unit"), None);
        assert_eq!(UnitRegistry::lookup("km"), None); // SI prefix not in registry
        assert_eq!(UnitRegistry::lookup("cm"), None); // CGS not in registry
    }

    // Synthetic UnitExpr fixtures for `eval_unit_expr` tests. Spans here
    // do not point at any real source; the evaluator reads them only for
    // diag attachment, and tests assert messages, not span ranges. A
    // single zero-length span is used uniformly so the convention is
    // visibly "synthetic" rather than mixing `(0, name.len())` /
    // `(0, 1)` ad-hoc.
    fn synthetic_span() -> crate::source::Span {
        crate::source::Span::new(0, 0)
    }

    fn unit_atom(name: &str) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Atom(name.into()),
            span: synthetic_span(),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_mul(a: crate::ast::UnitExpr, b: crate::ast::UnitExpr) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Mul(Box::new(a), Box::new(b)),
            span: synthetic_span(),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_div(a: crate::ast::UnitExpr, b: crate::ast::UnitExpr) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Div(Box::new(a), Box::new(b)),
            span: synthetic_span(),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_pow(base: crate::ast::UnitExpr, n: i64) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Pow(Box::new(base), n),
            span: synthetic_span(),
            id: crate::ids::NodeId(0),
        }
    }

    #[test]
    fn eval_unit_expr_atom_kg() {
        let u = unit_atom("kg");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([0, 1, 0, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }

    #[test]
    fn eval_unit_expr_unknown_atom_emits_diag_returns_err() {
        let u = unit_atom("xyz_unit");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Err(()));
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unknown unit"));
        assert!(diags[0].message.contains("xyz_unit"));
    }

    #[test]
    fn eval_unit_expr_mul_combines_dimensions() {
        // m * s → [1, 0, 1, 0, 0, 0, 0]
        let u = unit_mul(unit_atom("m"), unit_atom("s"));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([1, 0, 1, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }

    #[test]
    fn eval_unit_expr_div_subtracts_dimensions() {
        // m / s → [1, 0, -1, 0, 0, 0, 0]
        let u = unit_div(unit_atom("m"), unit_atom("s"));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([1, 0, -1, 0, 0, 0, 0])));
    }

    #[test]
    fn eval_unit_expr_pow_multiplies_exponent() {
        // m^2 → [2, 0, 0, 0, 0, 0, 0]
        let u = unit_pow(unit_atom("m"), 2);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([2, 0, 0, 0, 0, 0, 0])));
    }

    #[test]
    fn eval_unit_expr_negative_exponent() {
        // s^-1 (frequency) → [0, 0, -1, 0, 0, 0, 0]
        let u = unit_pow(unit_atom("s"), -1);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([0, 0, -1, 0, 0, 0, 0])));
    }

    #[test]
    fn eval_unit_expr_compound_meters_per_second_squared() {
        // m / s^2 → [1, 0, -2, 0, 0, 0, 0] (acceleration)
        let u = unit_div(unit_atom("m"), unit_pow(unit_atom("s"), 2));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([1, 0, -2, 0, 0, 0, 0])));
    }

    #[test]
    fn eval_unit_expr_overflow_emits_dimension_overflow_diag() {
        // m^100 → element 100, then ^2 = 200 overflows i8.
        let u = unit_pow(unit_pow(unit_atom("m"), 100), 2);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Err(()));
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("dimension component overflow"));
    }

    #[test]
    fn eval_unit_expr_exponent_out_of_i8_range_diag() {
        // kg^1000 — exponent literal 1000 > i8::MAX = 127.
        let u = unit_pow(unit_atom("kg"), 1000);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Err(()));
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("out of valid range"));
        assert!(diags[0].message.contains("1000"));
    }

    #[test]
    fn eval_unit_expr_derived_unit_lookup_force() {
        // N → [1, 1, -2, 0, 0, 0, 0] (Newton)
        let u = unit_atom("N");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Ok(Dimension([1, 1, -2, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }
}
