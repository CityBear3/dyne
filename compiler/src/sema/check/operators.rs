//! Operator typing and dimension-propagation rules (Q4–Q13).
//!
//! Split out of `check.rs` in the 2026-07 sema refactor. Owns the binary
//! and unary operator rules — arithmetic with unit propagation, `^`,
//! comparison, and logical ops — plus the small private helpers they use.
//! Methods run on `TypeChecker` (defined in the parent `check` module) and
//! are `pub(super)` so the bidirectional driver can dispatch to them.

use super::TypeChecker;
use crate::ast::{BinOp, Expr, ExprKind, UnaryOp};
use crate::diag::Diagnostic;
use crate::sema::dimension::{Dimension, OverflowError};
use crate::sema::ty::Ty;
use crate::source::Span;

impl TypeChecker<'_> {
    pub(super) fn synth_binop(&mut self, op: BinOp, l: &Expr, r: &Expr) -> Ty {
        let lt = self.synth_expr(l);
        let rt = self.synth_expr(r);
        if matches!(lt, Ty::Error) || matches!(rt, Ty::Error) {
            return Ty::Error;
        }
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                self.synth_arith(op, &lt, &rt, l.span, r.span)
            }
            // Pow takes the exponent expression (not just its type) so it can
            // require an integer literal; `rt` is computed/recorded above but
            // synth_pow reads `r`'s syntactic form for the literal value.
            BinOp::Pow => self.synth_pow(&lt, r, l.span),
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.synth_comparison(&lt, &rt, l.span)
            }
            BinOp::And | BinOp::Or => self.synth_logical(&lt, &rt, l.span, r.span),
        }
    }

    pub(super) fn synth_unaryop(&mut self, op: UnaryOp, x: &Expr) -> Ty {
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
                        self.definitions,
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
                        self.definitions,
                        x.span,
                        "unary `not`",
                        &xt,
                    ));
                    Ty::Error
                }
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
    /// Vec rules (Q5): `+`/`-` require equal shape AND equal dimension
    /// (shape-first diagnostic, no cascade); `Vec * Scalar` / `Scalar * Vec`
    /// multiply the dimension (commutative); `Vec / Scalar` divides it; every
    /// other Vec pairing (`Vec * Vec`, `Vec / Vec`, `Vec +/- Scalar`,
    /// `Scalar / Vec`) is rejected (use `dot()` / `cross()` for products).
    ///
    /// Mat rules (Q6): Mat is dimensionless per spec §4.4. `+`/`-` require
    /// equal shape; `Mat<m,n> * Mat<n,p>` → `Mat<m,p>`; `Mat<m,n> * Vec<n,d>`
    /// → `Vec<m,d>` (Mat dimensionless, Vec dimension transparent — replaces
    /// the PR-3b/3c arm-order placeholder per Q6-4); `Mat * Scalar` /
    /// `Mat / Scalar` require a dimensionless Scalar (else `dimension_mismatch`).
    /// `Vec * Mat` and `Mat / Mat` are rejected.
    ///
    /// On the result-shape choice: an arithmetic arm returns its computed
    /// shape (NOT `Ty::Error`) on a dimension/shape match so a cross-context
    /// mismatch still surfaces an accurate "expected T, found U" diagnostic
    /// rather than being swallowed (pinned by `vec_add_in_int_context_emits_diag`
    /// and the `*_wrong_return_dim_emits_diag` guards).
    pub(super) fn synth_arith(
        &mut self,
        op: BinOp,
        l: &Ty,
        r: &Ty,
        l_span: Span,
        r_span: Span,
    ) -> Ty {
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
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Scalar * Scalar / Scalar: dimension arithmetic.
            (BinOp::Mul, Ty::Scalar(d1), Ty::Scalar(d2)) => self
                .dim_op_result(d1.mul(*d2), l_span)
                .map_or(Ty::Error, Ty::Scalar),
            (BinOp::Div, Ty::Scalar(d1), Ty::Scalar(d2)) => self
                .dim_op_result(d1.div(*d2), l_span)
                .map_or(Ty::Error, Ty::Scalar),

            // Q6: Mat rules. Mat is dimensionless per spec §4.4. Placed
            // before the Vec arms so any Mat-involving pair is resolved here
            // (so e.g. Vec * Mat is rejected, not mistaken for a Vec op).

            // Mat +/- Mat: same shape required.
            (BinOp::Add | BinOp::Sub, Ty::Mat(m1, n1), Ty::Mat(m2, n2)) => {
                if m1 == m2 && n1 == n2 {
                    Ty::Mat(*m1, *n1)
                } else {
                    self.diagnostics.push(crate::sema::diag::shape_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Mat * Mat: Mat<m,n> * Mat<n,p> → Mat<m,p> (inner dims must match).
            (BinOp::Mul, Ty::Mat(m, n1), Ty::Mat(n2, p)) => {
                if n1 == n2 {
                    Ty::Mat(*m, *p)
                } else {
                    self.diagnostics.push(crate::sema::diag::shape_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Mat * Vec: Mat<m,n> * Vec<n,d> → Vec<m,d> (Mat dimensionless,
            // Vec dim transparent). REPLACES the PR-3b placeholder that
            // returned Mat<m,n> for this case (PR-3c CQ Minor; Q6-4).
            (BinOp::Mul, Ty::Mat(m, n1), Ty::Vec(n2, d)) => {
                if n1 == n2 {
                    Ty::Vec(*m, *d)
                } else {
                    self.diagnostics.push(crate::sema::diag::shape_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Mat * Scalar / Scalar * Mat (commutative) and Mat / Scalar: the
            // Scalar must be dimensionless (Mat stays dimensionless). Q11=A's
            // Int-promoted Scalar(ZERO) is dimensionless, so `2 * m`, `m * 2`,
            // `m / 2` scale cleanly; a dim-carrying Scalar → dimension_mismatch.
            (BinOp::Mul, Ty::Mat(m, n), Ty::Scalar(d))
            | (BinOp::Mul, Ty::Scalar(d), Ty::Mat(m, n))
            | (BinOp::Div, Ty::Mat(m, n), Ty::Scalar(d)) => {
                if d.is_dimensionless() {
                    Ty::Mat(*m, *n)
                } else {
                    self.diagnostics.push(crate::sema::diag::dimension_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                }
            }

            // Every other Mat involvement is rejected: Vec * Mat (Q6-2),
            // Mat / Mat (matrix inverse deferred), Scalar / Mat, Mat +/- Vec,
            // Mat +/- Scalar, etc.
            (_, Ty::Mat(_, _), _) | (_, _, Ty::Mat(_, _)) => {
                self.diagnostics.push(crate::sema::diag::type_mismatch(
                    l_span,
                    "Mat operation not supported for these operands (Mat +/- Mat requires equal shape; Mat * Mat, Mat * Vec, and Mat scaled by a dimensionless Scalar are supported; matrix division/inverse and Vec * Mat are not)",
                ));
                Ty::Error
            }

            // Q5: Vec rules.
            //
            // Vec +/- Vec: same shape AND same dim. Shape is checked first
            // so a shape-and-dim double mismatch yields a single (shape)
            // diagnostic, no cascade (Q5-4).
            (BinOp::Add | BinOp::Sub, Ty::Vec(n1, d1), Ty::Vec(n2, d2)) => {
                if n1 != n2 {
                    self.diagnostics.push(crate::sema::diag::shape_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                } else if d1 != d2 {
                    self.diagnostics.push(crate::sema::diag::dimension_mismatch(
                        self.definitions,
                        op_symbol(op),
                        l_span,
                        &l_eff,
                        r_span,
                        &r_eff,
                    ));
                    Ty::Error
                } else {
                    Ty::Vec(*n1, *d1)
                }
            }

            // Vec * Scalar / Scalar * Vec (commutative): dim multiplied.
            (BinOp::Mul, Ty::Vec(n, dv), Ty::Scalar(ds))
            | (BinOp::Mul, Ty::Scalar(ds), Ty::Vec(n, dv)) => self
                .dim_op_result(dv.mul(*ds), l_span)
                .map_or(Ty::Error, |d| Ty::Vec(*n, d)),

            // Vec / Scalar: dim divided. (Scalar / Vec is rejected below.)
            (BinOp::Div, Ty::Vec(n, dv), Ty::Scalar(ds)) => self
                .dim_op_result(dv.div(*ds), l_span)
                .map_or(Ty::Error, |d| Ty::Vec(*n, d)),

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

    /// Pow (`^`). The exponent must be an integer literal (DD §type-checker):
    /// - `Int ^ n`, `n >= 0` → `Int`; negative exponent → error (Q13: an Int
    ///   raised to a negative power is fractional — convert to a Scalar first)
    /// - `Scalar(d) ^ n` → `Scalar(d.pow(n))` (negative `n` is valid, e.g.
    ///   `Scalar<s> ^ -1` → `Scalar<s^-1>`)
    /// - `Vec(len, d) ^ n` → rejected (Q12: vector exponentiation is ambiguous;
    ///   use `dot(v, v)` / `norm(v)` for squared magnitude)
    /// - `Mat(m, m) ^ n`, `n >= 0` → `Mat(m, m)` (square + non-negative, Q6-3);
    ///   non-square or negative (matrix inverse) → error
    ///
    /// `base_ty` is the already-synthesized base type (synth_binop synthesized
    /// it); `exponent` is the raw expression so we can require a literal.
    pub(super) fn synth_pow(&mut self, base_ty: &Ty, exponent: &Expr, base_span: Span) -> Ty {
        // Q9 defense-in-depth: a failed-lowering base short-circuits.
        if matches!(base_ty, Ty::Error) {
            return Ty::Error;
        }

        // The exponent must be an integer literal. The expression parser
        // represents a negative literal as `Neg(IntLit)`, so accept both forms.
        let Some(n) = exponent_literal(exponent) else {
            self.diagnostics.push(Diagnostic::type_error(
                exponent.span,
                "`^` exponent must be an integer literal",
            ));
            return Ty::Error;
        };

        match base_ty {
            // Q13 (engineer decision): an Int raised to a negative power is
            // fractional (e.g. 2 ^ -1 = 0.5), which Int can't represent, so a
            // negative exponent is rejected for an Int base. (A Scalar base
            // keeps negative exponents — see below.)
            Ty::Int => {
                if n < 0 {
                    self.diagnostics.push(Diagnostic::type_error(
                        base_span,
                        "`^` on an Int with a negative exponent is not supported (convert to a float (Scalar) first)",
                    ));
                    Ty::Error
                } else {
                    Ty::Int
                }
            }
            Ty::Scalar(d) => self.pow_dim(*d, n, base_span).map_or(Ty::Error, Ty::Scalar),
            // Q12 (engineer decision): vector exponentiation is rejected —
            // it's ambiguous (componentwise vs. repeated dot product). Direct
            // users to `dot(v, v)` / `norm(v)` for squared magnitude.
            Ty::Vec(_, _) => {
                self.diagnostics.push(Diagnostic::type_error(
                    base_span,
                    "`^` on a Vec is not supported (vector exponentiation is ambiguous; use dot(v, v) or norm(v) for squared magnitude)",
                ));
                Ty::Error
            }
            Ty::Mat(m, cols) => {
                // Q6-3: square + non-negative only.
                if m != cols {
                    self.diagnostics.push(Diagnostic::type_error(
                        base_span,
                        format!("`^` on a Mat requires a square matrix, found Mat<{m}, {cols}>"),
                    ));
                    Ty::Error
                } else if n < 0 {
                    self.diagnostics.push(Diagnostic::type_error(
                        base_span,
                        "`^` on a Mat with a negative exponent (matrix inverse) is not supported",
                    ));
                    Ty::Error
                } else {
                    Ty::Mat(*m, *cols)
                }
            }
            _ => {
                self.diagnostics.push(crate::sema::diag::op_type_error(
                    self.definitions,
                    base_span,
                    "`^` base",
                    base_ty,
                ));
                Ty::Error
            }
        }
    }

    /// Resolve a `Dimension` arithmetic result for an operator: on overflow,
    /// push a `dimension_overflow` diag and return `None`; otherwise `Some(d)`.
    /// Shared by `synth_arith`'s Scalar/Vec `*` and `/` arms and `pow_dim`, so
    /// the overflow-diag boilerplate lives in one place. Callers map `Some`/
    /// `None` to the operand-shaped result `Ty` (`Ty::Scalar` / `Ty::Vec`) /
    /// `Ty::Error`.
    pub(super) fn dim_op_result(
        &mut self,
        result: Result<Dimension, OverflowError>,
        span: Span,
    ) -> Option<Dimension> {
        match result {
            Ok(d) => Some(d),
            Err(_) => {
                self.diagnostics
                    .push(crate::sema::diag::dimension_overflow(span));
                None
            }
        }
    }

    /// Raise a `Dimension` to an integer power for a `Scalar` base under `^`.
    /// Narrows the exponent to `i8` (out-of-range → `unit_exponent_out_of_range`)
    /// then applies `Dimension::pow` via `dim_op_result` (component overflow →
    /// `dimension_overflow`). Returns `None` (with a diag pushed) on either failure.
    pub(super) fn pow_dim(&mut self, d: Dimension, n: i64, span: Span) -> Option<Dimension> {
        let Ok(exp) = i8::try_from(n) else {
            self.diagnostics
                .push(crate::sema::diag::unit_exponent_out_of_range(span, n));
            return None;
        };
        self.dim_op_result(d.pow(exp), span)
    }

    pub(super) fn synth_comparison(&mut self, l: &Ty, r: &Ty, l_span: Span) -> Ty {
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

    pub(super) fn synth_logical(&mut self, l: &Ty, r: &Ty, l_span: Span, r_span: Span) -> Ty {
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
            self.definitions,
            span,
            "logical (`&&` / `||`)",
            offender,
        ));
        Ty::Error
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
/// - `Int op Mat` (Q11=A: Int scales Mat) → `Scalar op Mat`, so `2 * m` /
///   `m * 2` / `m / 2` route through the commutative `Mat * Scalar` and
///   `Mat / Scalar` arms (a dimensionless `Scalar(ZERO)` is admitted because
///   `Mat` is dimensionless per spec §4.4); `m + 2` falls to the Mat reject.
///
/// Non-mixed pairs pass through unchanged.
fn promote_int_to_scalar(l: &Ty, r: &Ty) -> (Ty, Ty) {
    match (l, r) {
        (Ty::Int, Ty::Scalar(_) | Ty::Vec(_, _) | Ty::Mat(_, _)) => {
            (Ty::Scalar(Dimension::ZERO), r.clone())
        }
        (Ty::Scalar(_) | Ty::Vec(_, _) | Ty::Mat(_, _), Ty::Int) => {
            (l.clone(), Ty::Scalar(Dimension::ZERO))
        }
        _ => (l.clone(), r.clone()),
    }
}

/// Extract an integer literal exponent from a `^` operand. The expression
/// parser represents a negative literal as `Neg(IntLit)` (unary minus binds
/// in `parse_prefix`), so both `n` (`IntLit`) and `-n` (`Neg(IntLit)`) are
/// recognized. Any other shape (variable, expression, double negation) →
/// `None`, which `synth_pow` reports as "exponent must be an integer literal".
fn exponent_literal(e: &Expr) -> Option<i64> {
    match &e.kind {
        ExprKind::IntLit(n) => Some(*n),
        ExprKind::UnaryOp(UnaryOp::Neg, inner) => match &inner.kind {
            ExprKind::IntLit(n) => Some(-n),
            _ => None,
        },
        _ => None,
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

#[cfg(test)]
mod tests {
    use crate::sema::check::test_support::{compile_src, diags_for};
    use crate::source::Span;

    // The unsupported-Vec-operation reject message, shared by the three
    // rejection cases below (Vec*Vec, Vec+Scalar broadcasting, Scalar/Vec).
    const VEC_REJECT_MSG: &str = "Vec operation not supported for these operands (Vec +/- Vec requires equal shape and dimension; use dot()/cross() for vector products; Vec scales by Scalar only)";

    // The unsupported-Mat-operation reject message, shared by Vec*Mat,
    // Mat/Mat, and other unsupported Mat operand combinations (Task 4).
    const MAT_REJECT_MSG: &str = "Mat operation not supported for these operands (Mat +/- Mat requires equal shape; Mat * Mat, Mat * Vec, and Mat scaled by a dimensionless Scalar are supported; matrix division/inverse and Vec * Mat are not)";

    // The Vec-exponentiation reject message (Q12), shared by the pow Vec tests.
    const POW_VEC_REJECT_MSG: &str = "`^` on a Vec is not supported (vector exponentiation is ambiguous; use dot(v, v) or norm(v) for squared magnitude)";

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
    fn dimension_mismatch_carries_operand_labels() {
        let src = "function f(a: Scalar<kg>, b: Scalar<m>): Scalar<kg>\n  return a + b\nend";
        let diags = diags_for(src);
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        let d = &diags[0];
        assert_eq!(d.labels.len(), 2, "labels: {:?}", d.labels);
        let a_pos = src.rfind("a + b").expect("operands in source");
        assert_eq!(
            d.labels[0].0,
            Span::new(a_pos, a_pos + 1),
            "left label span"
        );
        assert_eq!(
            d.labels[1].0,
            Span::new(a_pos + 4, a_pos + 5),
            "right label span"
        );
        assert_eq!(
            d.span,
            Span::merge(d.labels[0].0, d.labels[1].0),
            "merged primary"
        );
        assert!(d.labels[0].1.contains("left side"));
        assert!(d.labels[1].1.contains("right side"));
    }

    #[test]
    fn shape_mismatch_carries_operand_labels_with_spans() {
        let src = "function f(a: Vec<3>, b: Vec<2>): Vec<3>\n  return a + b\nend";
        let diags = diags_for(src);
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        let d = &diags[0];
        assert_eq!(d.labels.len(), 2, "labels: {:?}", d.labels);
        let a_pos = src.rfind("a + b").expect("operands in source");
        assert_eq!(
            d.labels[0].0,
            Span::new(a_pos, a_pos + 1),
            "left label span"
        );
        assert_eq!(
            d.labels[1].0,
            Span::new(a_pos + 4, a_pos + 5),
            "right label span"
        );
        assert_eq!(
            d.span,
            Span::merge(d.labels[0].0, d.labels[1].0),
            "merged primary"
        );
        assert!(d.labels[0].1.contains("left side"));
        assert!(d.labels[1].1.contains("right side"));
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
            "shape mismatch in '+': left side has Vec<3>, but right side has Vec<2>"
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
            "shape mismatch in '+': left side has Vec<3, m>, but right side has Vec<2, kg>"
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
    fn int_plus_vec_rejected() {
        // Q11=A is multiplicative-only: Int *scales* a Vec, it does not add
        // to it. `2 + v` promotes the Int to Scalar(ZERO), then Scalar + Vec
        // hits the Vec reject arm (no broadcasting). Pins the additive
        // boundary explicitly.
        let diags = diags_for("function f(v: Vec<3>): Vec<3>\n  return 2 + v\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, VEC_REJECT_MSG);
    }

    #[test]
    fn mat_add_same_shape_returns_mat() {
        compile_src("function f(a: Mat<2, 2>, b: Mat<2, 2>): Mat<2, 2>\n  return a + b\nend");
    }

    #[test]
    fn mat_add_shape_mismatch_diag() {
        let diags =
            diags_for("function f(a: Mat<2, 2>, b: Mat<3, 3>): Mat<2, 2>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "shape mismatch in '+': left side has Mat<2, 2>, but right side has Mat<3, 3>"
        );
    }

    #[test]
    fn mat_mul_mat_compatible_shapes_returns_mat() {
        // Mat<2,3> * Mat<3,4> → Mat<2,4>.
        compile_src("function f(a: Mat<2, 3>, b: Mat<3, 4>): Mat<2, 4>\n  return a * b\nend");
    }

    #[test]
    fn mat_mul_mat_shape_mismatch_diag() {
        // Inner dims disagree (3 cols vs 2 rows).
        let diags =
            diags_for("function f(a: Mat<2, 3>, b: Mat<2, 4>): Mat<2, 4>\n  return a * b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "shape mismatch in '*': left side has Mat<2, 3>, but right side has Mat<2, 4>"
        );
    }

    #[test]
    fn mat_mul_vec_returns_vec_with_dim_through() {
        // Mat<2,3> * Vec<3, m/s> → Vec<2, m/s> (Mat dimensionless, Vec dim
        // transparent).
        compile_src("function f(m: Mat<2, 3>, v: Vec<3, m/s>): Vec<2, m/s>\n  return m * v\nend");
    }

    #[test]
    fn mat_mul_vec_arm_order_placeholder_replaced() {
        // PR-3c CQ Minor: the PR-3b placeholder returned a Mat shape for
        // Mat·Vec. Q6 replaces it with the correct Vec result. Rectangular
        // (Mat<2,3> * Vec<3> → Vec<2>) so the test is self-contained to its
        // name: a Mat<2,3>-shaped result would NOT unify with the Vec<2>
        // return, proving the arm yields Vec<m>, not the Mat shape.
        compile_src("function f(m: Mat<2, 3>, v: Vec<3>): Vec<2>\n  return m * v\nend");
    }

    #[test]
    fn mat_mul_vec_shape_mismatch_diag() {
        // Mat<2,3> * Vec<2> — inner dim 3 != 2.
        let diags = diags_for("function f(m: Mat<2, 3>, v: Vec<2>): Vec<2>\n  return m * v\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "shape mismatch in '*': left side has Mat<2, 3>, but right side has Vec<2>"
        );
    }

    #[test]
    fn mat_mul_scalar_dimensionless_returns_mat() {
        // Q6: Mat * Scalar(ZERO) allowed (Mat stays dimensionless).
        compile_src("function f(m: Mat<2, 2>, s: Scalar): Mat<2, 2>\n  return m * s\nend");
    }

    #[test]
    fn mat_div_scalar_dimensionless_returns_mat() {
        // Q6: Mat / Scalar(ZERO) allowed (Mat stays dimensionless),
        // mirroring the Mul guard above.
        compile_src("function f(m: Mat<2, 2>, s: Scalar): Mat<2, 2>\n  return m / s\nend");
    }

    #[test]
    fn mat_mul_scalar_with_dim_rejected_diag() {
        // Q6: Mat * Scalar<m/s> rejected (Mat must stay dimensionless).
        let diags =
            diags_for("function f(m: Mat<2, 2>, s: Scalar<m/s>): Mat<2, 2>\n  return m * s\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension mismatch in '*': left side has Mat<2, 2>, but right side has Scalar<m*s^-1>"
        );
    }

    #[test]
    fn scalar_with_dim_mul_mat_rejected_diag() {
        // Commutative-order mirror of mat_mul_scalar_with_dim_rejected_diag:
        // Scalar<m/s> * Mat is also rejected (Mat must stay dimensionless).
        let diags =
            diags_for("function f(m: Mat<2, 2>, s: Scalar<m/s>): Mat<2, 2>\n  return s * m\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension mismatch in '*': left side has Scalar<m*s^-1>, but right side has Mat<2, 2>"
        );
    }

    #[test]
    fn vec_mul_mat_rejected() {
        // Q6-2: Vec * Mat rejected (only Mat * Vec is defined).
        let diags = diags_for("function f(m: Mat<2, 3>, v: Vec<2>): Vec<2>\n  return v * m\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, MAT_REJECT_MSG);
    }

    #[test]
    fn mat_div_mat_rejected() {
        // Mat / Mat rejected (matrix inverse / division deferred).
        let diags =
            diags_for("function f(a: Mat<2, 2>, b: Mat<2, 2>): Mat<2, 2>\n  return a / b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, MAT_REJECT_MSG);
    }

    #[test]
    fn int_mul_mat_scales() {
        compile_src("function f(m: Mat<2, 2>): Mat<2, 2>\n  return 2 * m\nend");
    }

    #[test]
    fn mat_mul_int_scales() {
        compile_src("function f(m: Mat<2, 2>): Mat<2, 2>\n  return m * 2\nend");
    }

    #[test]
    fn mat_div_int_scales() {
        compile_src("function f(m: Mat<2, 2>): Mat<2, 2>\n  return m / 2\nend");
    }

    #[test]
    fn scalar_mul_mat_still_works_regression() {
        // 2.0 * m (Scalar * Mat, commutative) still yields Mat<2, 2>.
        compile_src("function f(m: Mat<2, 2>): Mat<2, 2>\n  return 2.0 * m\nend");
    }

    #[test]
    fn int_plus_mat_rejected() {
        // Q11=A multiplicative-only boundary for Mat: `2 + m` promotes the
        // Int to Scalar(ZERO), then Scalar + Mat hits the Mat reject arm.
        let diags = diags_for("function f(m: Mat<2, 2>): Mat<2, 2>\n  return 2 + m\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, MAT_REJECT_MSG);
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
        // Pow base = Int, non-negative exponent → Int. Function expects Int
        // return, so unify succeeds.
        compile_src("function f(): Int\n  return 2 ^ 3\nend");
    }

    #[test]
    fn pow_int_zero_exponent_returns_int() {
        // Boundary: n == 0 is non-negative → Int (guards the n < 0 cutoff).
        compile_src("function f(): Int\n  return 2 ^ 0\nend");
    }

    #[test]
    fn int_pow_negative_rejected() {
        // Q13: Int ^ negative is fractional (2 ^ -1 = 0.5) — rejected for an
        // Int base. (Scalar ^ negative stays valid; see pow_scalar_negative.)
        let diags = diags_for("function f(): Int\n  return 2 ^ -1\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "`^` on an Int with a negative exponent is not supported (convert to a float (Scalar) first)"
        );
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
    fn pow_scalar_kg_squared_returns_kg_squared() {
        // Scalar<kg> ^ 2 → Scalar<kg^2> (dim propagates through `^`).
        compile_src("function f(m: Scalar<kg>): Scalar<kg^2>\n  return m ^ 2\nend");
    }

    #[test]
    fn pow_scalar_negative_exponent() {
        // Scalar<s> ^ -1 → Scalar<s^-1>. The expression parser represents the
        // exponent as Neg(IntLit(1)); exponent_literal recovers -1.
        compile_src("function f(t: Scalar<s>): Scalar<s^-1>\n  return t ^ -1\nend");
    }

    #[test]
    fn pow_non_intlit_exponent_diag() {
        // DD §type-checker: a non-literal exponent is a type error.
        let diags = diags_for("function f(): Int\n  let n: Int = 2\n  return 2 ^ n\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, "`^` exponent must be an integer literal");
    }

    #[test]
    fn pow_vec_rejected_diag() {
        // Q12 (engineer decision): vector exponentiation is rejected as
        // ambiguous. `v ^ 2` → reject (use dot()/norm() for squared magnitude).
        let diags = diags_for("function f(v: Vec<3, m>): Vec<3, m>\n  return v ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, POW_VEC_REJECT_MSG);
    }

    #[test]
    fn pow_square_mat_nonneg_returns_mat() {
        // Q6-3: Mat<3,3> ^ 2 → Mat<3,3>.
        compile_src("function f(m: Mat<3, 3>): Mat<3, 3>\n  return m ^ 2\nend");
    }

    #[test]
    fn pow_non_square_mat_diag() {
        // Q6-3: Mat<2,3> ^ 2 — non-square, rejected.
        let diags = diags_for("function f(m: Mat<2, 3>): Mat<2, 3>\n  return m ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "`^` on a Mat requires a square matrix, found Mat<2, 3>"
        );
    }

    #[test]
    fn pow_mat_negative_exponent_diag() {
        // Q6-3: Mat ^ -1 (matrix inverse) deferred → rejected.
        let diags = diags_for("function f(m: Mat<3, 3>): Mat<3, 3>\n  return m ^ -1\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "`^` on a Mat with a negative exponent (matrix inverse) is not supported"
        );
    }

    #[test]
    fn pow_scalar_dim_overflow_diag() {
        // Scalar<m^2> ^ 100 → element 2*100 = 200 overflows i8 in
        // Dimension::pow (the exponent 100 is itself in i8 range).
        let diags = diags_for("function f(x: Scalar<m^2>): Scalar\n  return x ^ 100\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "dimension component overflow in unit expression"
        );
    }

    #[test]
    fn pow_scalar_exponent_out_of_i8_range_diag() {
        // Exponent 200 > i8::MAX (127) — rejected before the dim pow.
        let diags = diags_for("function f(x: Scalar<m>): Scalar\n  return x ^ 200\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "unit exponent 200 out of valid range [-128, 127]"
        );
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
        // Originally a placeholder-seam pin (synth_pow stripped Vec dim and
        // let the Int-return context surface the mismatch). PR-3d-β Task 5 +
        // Q12 reject Vec exponentiation outright, so the single diag now comes
        // from the `^`-on-Vec reject path (and return-type unify suppresses on
        // Ty::Error — no cascade).
        let diags = diags_for("function f(v: Vec<3>): Int\n  return v ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(diags[0].message, POW_VEC_REJECT_MSG);
    }

    // Success-arm regression guards (mirror `vec_add_in_int_context_emits_diag`
    // for the mul / div / pow dimension-propagation arms). Each program's
    // operator arm computes a concrete result type that must then mismatch the
    // declared return type, surfacing exactly one cross-context diagnostic. If
    // the success arm silently regressed to `Ty::Error`, that `Ty::Error`
    // unifies with anything and NO diagnostic would fire — these tests catch
    // that.

    #[test]
    fn scalar_mul_wrong_return_dim_emits_diag() {
        // `a * b` = Scalar<m*kg>; reverting the Scalar-Mul success arm to
        // Ty::Error would re-break this (the m*kg ≠ s mismatch would vanish).
        let diags =
            diags_for("function f(a: Scalar<kg>, b: Scalar<m>): Scalar<s>\n  return a * b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Scalar<s>`, found `Scalar<m*kg>`"
        );
    }

    #[test]
    fn vec_scale_wrong_return_dim_emits_diag() {
        // `v * t` = Vec<3, m*s>; reverting the Vec*Scalar success arm to
        // Ty::Error would re-break this.
        let diags =
            diags_for("function f(v: Vec<3, m>, t: Scalar<s>): Vec<3, kg>\n  return v * t\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Vec<3, kg>`, found `Vec<3, m*s>`"
        );
    }

    #[test]
    fn scalar_pow_wrong_return_dim_emits_diag() {
        // `x ^ 2` = Scalar<kg^2>; reverting the Scalar-pow success arm to
        // Ty::Error would re-break this.
        let diags = diags_for("function f(x: Scalar<kg>): Scalar<m>\n  return x ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Scalar<m>`, found `Scalar<kg^2>`"
        );
    }

    #[test]
    fn scalar_div_wrong_return_dim_emits_diag() {
        // `a / b` = Scalar<kg*s^-1>; reverting the Scalar-Div success arm to
        // Ty::Error would re-break this (the kg*s^-1 ≠ m mismatch would vanish).
        let diags =
            diags_for("function f(a: Scalar<kg>, b: Scalar<s>): Scalar<m>\n  return a / b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Scalar<m>`, found `Scalar<kg*s^-1>`"
        );
    }

    #[test]
    fn vec_div_scalar_wrong_return_dim_emits_diag() {
        // `v / t` = Vec<3, m*s^-1>; reverting the Vec/Scalar-Div success arm to
        // Ty::Error would re-break this.
        let diags =
            diags_for("function f(v: Vec<3, m>, t: Scalar<s>): Vec<3, kg>\n  return v / t\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Vec<3, kg>`, found `Vec<3, m*s^-1>`"
        );
    }

    #[test]
    fn mat_mul_mat_wrong_return_shape_emits_diag() {
        // `a * b` = Mat<2, 4>; reverting the Mat*Mat success arm to Ty::Error
        // would re-break this (the 2x4 ≠ 3x4 shape mismatch would vanish).
        let diags =
            diags_for("function f(a: Mat<2, 3>, b: Mat<3, 4>): Mat<3, 4>\n  return a * b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Mat<3, 4>`, found `Mat<2, 4>`"
        );
    }

    #[test]
    fn mat_mul_vec_wrong_return_dim_emits_diag() {
        // `m * v` = Vec<2, m*s^-1>; reverting the Mat*Vec success arm to
        // Ty::Error would re-break this (and re-open the Q6-4 arm-order bug,
        // since the placeholder returned a Mat shape rather than a Vec).
        let diags =
            diags_for("function f(m: Mat<2, 3>, v: Vec<3, m/s>): Vec<2, kg>\n  return m * v\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Vec<2, kg>`, found `Vec<2, m*s^-1>`"
        );
    }

    #[test]
    fn mat_mul_scalar_wrong_return_shape_emits_diag() {
        // `a * s` = Mat<2, 3> (dimensionless Scalar leaves the shape intact);
        // reverting the Mat*Scalar success arm to Ty::Error would re-break this
        // (the 2x3 ≠ 3x2 shape mismatch would vanish).
        let diags =
            diags_for("function f(a: Mat<2, 3>, s: Scalar): Mat<3, 2>\n  return a * s\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Mat<3, 2>`, found `Mat<2, 3>`"
        );
    }

    #[test]
    fn scalar_add_wrong_return_dim_emits_diag() {
        // `a + b` = Scalar<kg> (equal-dim success arm); reverting the
        // Scalar-Add/Sub success arm to Ty::Error would re-break this (the
        // kg ≠ m mismatch against the declared return would vanish).
        let diags =
            diags_for("function f(a: Scalar<kg>, b: Scalar<kg>): Scalar<m>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Scalar<m>`, found `Scalar<kg>`"
        );
    }

    #[test]
    fn mat_add_wrong_return_shape_emits_diag() {
        // `a + b` = Mat<2, 3> (equal-shape success arm); reverting the
        // Mat-Add/Sub success arm to Ty::Error would re-break this (the
        // 2x3 ≠ 3x2 mismatch against the declared return would vanish).
        let diags =
            diags_for("function f(a: Mat<2, 3>, b: Mat<2, 3>): Mat<3, 2>\n  return a + b\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Mat<3, 2>`, found `Mat<2, 3>`"
        );
    }

    #[test]
    fn mat_pow_wrong_return_shape_emits_diag() {
        // `m ^ 2` = Mat<2, 2> (square + non-negative success arm); reverting
        // the Mat-pow success arm to Ty::Error would re-break this (the
        // 2x2 ≠ 3x3 mismatch against the declared return would vanish).
        let diags = diags_for("function f(m: Mat<2, 2>): Mat<3, 3>\n  return m ^ 2\nend");
        assert_eq!(diags.len(), 1, "diags: {diags:?}");
        assert_eq!(
            diags[0].message,
            "type mismatch: expected `Mat<3, 3>`, found `Mat<2, 2>`"
        );
    }
}
