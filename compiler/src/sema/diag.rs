//! Diagnostic constructors for the sema phase.

use crate::diag::Diagnostic;
use crate::sema::resolve::DefKind;
use crate::sema::ty::Ty;
use crate::source::Span;

pub fn undefined_name(span: Span, name: &str) -> Diagnostic {
    Diagnostic::type_error(span, format!("undefined name `{name}`"))
}

pub fn duplicate_name(span: Span, prev_span: Span, name: &str) -> Diagnostic {
    Diagnostic::type_error(span, format!("`{name}` is already defined in this scope"))
        .with_label(prev_span, "previously defined here")
}

/// "expected `<expected>`, found `<actual>`" — used by `unify_or_diag` when
/// the synthesized type doesn't match the checking-mode expectation.
pub fn type_mismatch_full(span: Span, expected: &Ty, actual: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "type mismatch: expected `{}`, found `{}`",
            format_ty(expected),
            format_ty(actual)
        ),
    )
}

/// Per-operator structural mismatch (e.g. "arithmetic operands must both
/// be Int or Scalar").
pub fn type_mismatch(span: Span, msg: &str) -> Diagnostic {
    Diagnostic::type_error(span, msg.to_string())
}

pub fn op_type_error(span: Span, op_desc: &str, ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("{op_desc} not defined for `{}`", format_ty(ty)),
    )
}

pub fn non_bool_condition(span: Span, ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("expected `Bool` for condition, found `{}`", format_ty(ty)),
    )
}

pub fn wrong_arity(span: Span, expected: usize, actual: usize) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("wrong number of arguments: expected {expected}, found {actual}"),
    )
}

/// Generic-type instantiation arity mismatch, e.g. `Result<Int>` when the
/// declaration is `enum Result<T, E>`. Used by `lower_type` to point at the
/// annotation site rather than letting the mismatch cascade through later
/// passes as a vague "type error".
pub fn wrong_type_arity(span: Span, name: &str, expected: usize, actual: usize) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("`{name}` expects {expected} type argument(s), but {actual} were provided"),
    )
}

pub fn not_callable(span: Span, ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(span, format!("type `{}` is not callable", format_ty(ty)))
}

pub fn field_unknown(span: Span, struct_name: &str, field: &str) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("struct `{struct_name}` has no field `{field}`"),
    )
}

pub fn missing_struct_field(span: Span, struct_name: &str, field: &str) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("missing field `{field}` in struct `{struct_name}` literal"),
    )
}

pub fn extra_struct_field(span: Span, struct_name: &str, field: &str) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("struct `{struct_name}` has no field `{field}`; extra field in literal"),
    )
}

/// Type name (struct / enum) used in a value position. `synth_ident`
/// emits this when an identifier resolves to a type-level definition
/// rather than a runtime binding. `DefKind::EnumVariant` is intentionally
/// omitted — variant-as-value typing is a documented PR-3c deferral.
pub fn not_a_value(span: Span, kind: DefKind, name: &str) -> Diagnostic {
    let kind_str = match kind {
        DefKind::Struct => "struct type",
        DefKind::Enum => "enum type",
        // Defensive: callers should only pass Struct/Enum. Other kinds
        // either have a `def_types` entry (Function/Param/Let/LoopVar/
        // PatternBinding) or are deferred to PR-3c (EnumVariant).
        _ => "type",
    };
    Diagnostic::type_error(span, format!("`{name}` is a {kind_str}, not a value"))
}

/// `expected` is the declared `(rows, cols)`; `actual_cols` is the
/// length of the offending row. The previous signature passed the row
/// count alongside the column count for the actual shape, but every
/// call site computed the row count as `rows.len()` (the same value
/// `expected.0` carried), so the diag never read it. Simplified to
/// take only the column count of the row that triggered the error.
pub fn mat_shape_mismatch(span: Span, expected: (usize, usize), actual_cols: usize) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "matrix shape mismatch: expected {} rows × {} cols, found a row with {} cells",
            expected.0, expected.1, actual_cols
        ),
    )
}

/// Match-pattern fired against a scrutinee whose type is not an enum.
/// `expected_kind` is the pattern's expected category (e.g. "enum") so the
/// message reads naturally — the scrutinee's type comes from `actual`.
pub fn pattern_type_mismatch(span: Span, actual: &Ty, expected_kind: &str) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "pattern matches {expected_kind} but scrutinee is `{}`",
            format_ty(actual)
        ),
    )
}

/// Variant pattern referencing a variant that doesn't belong to the
/// scrutinee's enum. e.g. `case Some(x)` against a `Result<_, _>`
/// scrutinee — `Some` is from `Maybe`, not `Result`.
pub fn wrong_variant_for_enum(span: Span, variant_name: &str, scrut_ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "variant `{variant_name}` does not belong to scrutinee type `{}`",
            format_ty(scrut_ty)
        ),
    )
}

/// Match expression doesn't cover every variant of its enum scrutinee.
/// `missing_variants` lists the variant names (in declaration order)
/// that have no covering arm.
pub fn non_exhaustive_enum(span: Span, missing_variants: &[&str]) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "non-exhaustive match: missing variant(s) {}",
            missing_variants.join(", ")
        ),
    )
}

/// Match expression on `Bool` doesn't cover both `true` and `false`
/// (and has no catch-all).
pub fn non_exhaustive_bool(span: Span, missing: &[&str]) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "non-exhaustive match on Bool: missing {}",
            missing.join(", ")
        ),
    )
}

/// Match expression on a scrutinee whose type doesn't have a finite
/// canonical pattern set (Int, Scalar, String, Vec, Mat, Array, Dict)
/// — exhaustiveness can only be guaranteed by an explicit catch-all
/// pattern (`_` or an Ident binding).
pub fn requires_wildcard(span: Span, kind: &str) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "non-exhaustive match on `{kind}`: a wildcard pattern (`_` or binding) is required"
        ),
    )
}

/// Reported when a `Dimension` arithmetic operation overflows i8 element
/// bounds during unit-expression evaluation. The site that detected the
/// overflow substitutes `Dimension::ZERO` to suppress cascade.
pub fn dimension_overflow(span: Span) -> Diagnostic {
    Diagnostic::type_error(span, "dimension component overflow in unit expression")
}

/// Reported when a unit exponent literal is outside the valid i8 range
/// `[-128, 127]`. Realistic physics exponents fit in ±8; values outside
/// this range are almost certainly typos or computation errors.
pub fn unit_exponent_out_of_range(span: Span, n: i64) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("unit exponent {n} out of valid range [-128, 127]"),
    )
}

/// Reported when a unit atom name is not in the built-in registry.
/// Per PR-3d-α scope (Q3), only SI base 7 + 8 derived units are
/// recognized. SI prefixes / CGS / user-defined units are deferred.
pub fn unknown_unit(span: Span, name: &str) -> Diagnostic {
    Diagnostic::type_error(span, format!("unknown unit `{name}`"))
}

/// Reported when two operands of a binary operator have incompatible
/// dimensions (e.g., `Scalar<kg> + Scalar<m>`), or when a context-required
/// dimensionality is violated (e.g., `Mat<3,3> * Scalar<m/s>` where a `Mat`
/// must remain dimensionless per spec §4.4).
///
/// Per /design-discussion 2026-05-08 Q4-3, the message is operator-focus:
/// it names the op symbol and shows both sides via `format_ty`, which
/// renders a dim-carrying `Scalar` / `Vec` with its SI unit (e.g.
/// `Scalar<kg>`). Single unified helper covers Scalar Add/Sub, Vec Add/Sub,
/// Mat dim violations, and Int→Scalar implicit-conversion failures (Q7-A).
pub fn dimension_mismatch(span: Span, op: &str, lhs: &Ty, rhs: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "dimension mismatch in '{op}': left side has {}, but right side has {}",
            format_ty(lhs),
            format_ty(rhs),
        ),
    )
}

/// Reported when two `Vec` operands of `+` / `-` have different lengths
/// (e.g. `Vec<3> + Vec<2>`). Binary-op symmetric — names both sides'
/// lengths rather than an "expected" side. Per Q5-4 this fires *before*
/// any dimension check so a shape-and-dim double mismatch surfaces a
/// single (shape) diagnostic with no cascade.
pub fn shape_mismatch_vec(span: Span, left_len: usize, right_len: usize) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "Vec shape mismatch: left side has length {left_len}, but right side has length {right_len}"
        ),
    )
}

/// Reported when a `Mat`-involving binary op has incompatible operand shapes:
/// `Mat +/- Mat` of different dimensions, a `Mat * Mat` whose inner dims
/// disagree, or a `Mat * Vec` whose column count ≠ the Vec length. Operator-
/// focus (like [`dimension_mismatch`]): names the op and renders both operands
/// via `format_ty` so the offending shapes are visible.
pub fn shape_mismatch_mat(span: Span, op: &str, lhs: &Ty, rhs: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "shape mismatch in '{op}': left side has {}, but right side has {}",
            format_ty(lhs),
            format_ty(rhs),
        ),
    )
}

/// Render a `Ty` for diagnostic messages. Dim-carrying `Scalar` / `Vec`
/// render their SI unit via [`Dimension::format_si`] (e.g. `Scalar<kg>`,
/// `Vec<3, m*s^-1>`); dimensionless ones elide the unit (`Scalar`,
/// `Vec<3>`), matching the source convention that omission = dimensionless.
fn format_ty(ty: &Ty) -> String {
    match ty {
        Ty::Int => "Int".into(),
        Ty::Scalar(d) => {
            if d.is_dimensionless() {
                "Scalar".into()
            } else {
                format!("Scalar<{}>", d.format_si())
            }
        }
        Ty::Bool => "Bool".into(),
        Ty::String => "String".into(),
        Ty::Vec(n, d) => {
            if d.is_dimensionless() {
                format!("Vec<{n}>")
            } else {
                format!("Vec<{n}, {}>", d.format_si())
            }
        }
        Ty::Mat(m, n) => format!("Mat<{m}, {n}>"),
        Ty::Array(t) => format!("Array<{}>", format_ty(t)),
        Ty::Dict(k, v) => format!("Dict<{}, {}>", format_ty(k), format_ty(v)),
        Ty::Function(args, ret) => {
            let arg_strs: Vec<String> = args.iter().map(format_ty).collect();
            format!("({}) -> {}", arg_strs.join(", "), format_ty(ret))
        }
        Ty::Struct(_) => "<struct>".into(),
        Ty::Enum(_, _) => "<enum>".into(),
        Ty::Var(_) => "?".into(),
        // Param should never reach diagnostic rendering — `synth_ident`
        // substitutes Param → fresh Var before the type can leak into a
        // diagnostic. The arm exists to keep `format_ty` exhaustive, and
        // the message names the schema position so a regression that lets
        // Param escape produces something readable rather than a panic.
        Ty::Param(i) => format!("<param #{i}>"),
        Ty::Error => "<error>".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::ty::{Dimension, Ty};
    use crate::source::Span;

    // These pin the FULL rendered message (not loose `contains`) so the
    // format_si unit integration introduced here can't silently regress:
    // a change dropping units from `format_ty` (e.g. back to bare
    // `Scalar` / `Vec<3>`) would still pass a `contains("Vec")`-style
    // check but fails these exact-match assertions.

    #[test]
    fn dimension_mismatch_scalar_add_kg_vs_m() {
        let lhs = Ty::Scalar(Dimension([0, 1, 0, 0, 0, 0, 0])); // kg
        let rhs = Ty::Scalar(Dimension([1, 0, 0, 0, 0, 0, 0])); // m
        let diag = dimension_mismatch(Span::new(0, 5), "+", &lhs, &rhs);
        assert_eq!(
            diag.message,
            "dimension mismatch in '+': left side has Scalar<kg>, but right side has Scalar<m>"
        );
    }

    #[test]
    fn dimension_mismatch_vec_dim_inconsistent() {
        let lhs = Ty::Vec(3, Dimension([1, 0, 0, 0, 0, 0, 0])); // m
        let rhs = Ty::Vec(3, Dimension([0, 1, 0, 0, 0, 0, 0])); // kg
        let diag = dimension_mismatch(Span::new(0, 5), "-", &lhs, &rhs);
        assert_eq!(
            diag.message,
            "dimension mismatch in '-': left side has Vec<3, m>, but right side has Vec<3, kg>"
        );
    }

    #[test]
    fn dimension_mismatch_mat_against_dim_scalar() {
        let lhs = Ty::Mat(3, 3);
        let rhs = Ty::Scalar(Dimension([1, 0, -1, 0, 0, 0, 0])); // m/s
        let diag = dimension_mismatch(Span::new(0, 5), "*", &lhs, &rhs);
        assert_eq!(
            diag.message,
            "dimension mismatch in '*': left side has Mat<3, 3>, but right side has Scalar<m*s^-1>"
        );
    }
}
