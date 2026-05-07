//! Diagnostic constructors for the sema phase.

use crate::diag::Diagnostic;
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
/// be Int or Scalar"). The second span lets future revisions point at the
/// disagreeing operand; not currently used for labelling but kept in the
/// signature so callers don't have to lose the location.
pub fn type_mismatch(span: Span, _other_span: Span, msg: &str) -> Diagnostic {
    Diagnostic::type_error(span, msg.to_string())
}

pub fn op_type_error(span: Span, op_desc: &str, ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("{op_desc} not defined for `{}`", format_ty(ty)),
    )
}

#[allow(dead_code)] // Used by control-flow rules in Task 6.
pub fn non_bool_condition(span: Span, ty: &Ty) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!("expected `Bool` for condition, found `{}`", format_ty(ty)),
    )
}

/// Render a `Ty` for diagnostic messages. PR-3b uses base names; PR-3d's
/// `Dimension::format_si` integrates here once units are implemented.
fn format_ty(ty: &Ty) -> String {
    match ty {
        Ty::Int => "Int".into(),
        Ty::Scalar(_) => "Scalar".into(),
        Ty::Bool => "Bool".into(),
        Ty::String => "String".into(),
        Ty::Vec(n, _) => format!("Vec<{n}>"),
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
        Ty::Error => "<error>".into(),
    }
}
