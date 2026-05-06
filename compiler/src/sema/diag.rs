//! Diagnostic constructors for the sema phase.

use crate::diag::Diagnostic;
use crate::source::Span;

pub fn undefined_name(span: Span, name: &str) -> Diagnostic {
    Diagnostic::type_error(span, format!("undefined name `{name}`"))
}

pub fn duplicate_name(span: Span, prev_span: Span, name: &str) -> Diagnostic {
    Diagnostic::type_error(span, format!("`{name}` is already defined in this scope"))
        .with_label(prev_span, "previously defined here")
}
