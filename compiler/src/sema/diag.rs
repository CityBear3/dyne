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

pub fn mat_shape_mismatch(
    span: Span,
    expected: (usize, usize),
    actual: (usize, usize),
) -> Diagnostic {
    Diagnostic::type_error(
        span,
        format!(
            "matrix shape mismatch: expected {} rows × {} cols, found a row with {} cells",
            expected.0, expected.1, actual.1
        ),
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
        // Param should never reach diagnostic rendering — `synth_ident`
        // substitutes Param → fresh Var before the type can leak into a
        // diagnostic. The arm exists to keep `format_ty` exhaustive, and
        // the message names the schema position so a regression that lets
        // Param escape produces something readable rather than a panic.
        Ty::Param(i) => format!("<param #{i}>"),
        Ty::Error => "<error>".into(),
    }
}
