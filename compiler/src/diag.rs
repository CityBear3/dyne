//! Compile-time diagnostic type.

use crate::source::{SourceFile, Span};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Lex,
    Parse,
    Sema,
}

impl Phase {
    fn label(self) -> &'static str {
        match self {
            Phase::Lex => "lex error",
            Phase::Parse => "parse error",
            Phase::Sema => "sema error",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub phase: Phase,
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    pub fn new(phase: Phase, span: Span, message: impl Into<String>) -> Self {
        Self {
            phase,
            span,
            message: message.into(),
        }
    }

    pub fn lex_error(span: Span, message: impl Into<String>) -> Self {
        Self::new(Phase::Lex, span, message)
    }

    pub fn parse_error(span: Span, message: impl Into<String>) -> Self {
        Self::new(Phase::Parse, span, message)
    }

    /// Render the diagnostic with line/column and source excerpt.
    pub fn render(&self, source: &SourceFile) -> String {
        let (line, col) = source.line_col(self.span.start);
        let kind = self.phase.label();
        let excerpt = source.line_text(line).unwrap_or("");
        let caret_col = col.saturating_sub(1);
        let caret = " ".repeat(caret_col) + "^";
        format!(
            "{kind} at line {line}, col {col}: {msg}\n{excerpt}\n{caret}",
            kind = kind,
            line = line,
            col = col,
            msg = self.message,
            excerpt = excerpt,
            caret = caret,
        )
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = self.phase.label();
        write!(f, "{kind} at offset {}: {}", self.span.start, self.message)
    }
}

impl std::error::Error for Diagnostic {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_points_to_line_and_column() {
        let src = SourceFile::new("let x = 1\nlet y = ?\nlet z = 3");
        let err = Diagnostic::lex_error(Span::new(18, 19), "unexpected character '?'");
        let rendered = err.render(&src);
        assert!(rendered.contains("line 2, col 9"));
        assert!(rendered.contains("let y = ?"));
        assert!(rendered.contains("unexpected character '?'"));
    }

    #[test]
    fn display_short_form() {
        let err = Diagnostic::parse_error(Span::new(5, 6), "expected ')'");
        assert_eq!(format!("{err}"), "parse error at offset 5: expected ')'");
    }

    #[test]
    fn render_for_parse_error() {
        let src = SourceFile::new("ab cd");
        let err = Diagnostic::parse_error(Span::new(3, 4), "expected '('");
        let rendered = err.render(&src);
        assert!(rendered.contains("parse error"));
        assert!(rendered.contains("expected '('"));
    }

    #[test]
    fn display_for_lex_error() {
        let err = Diagnostic::lex_error(Span::new(0, 1), "bad byte");
        assert_eq!(format!("{err}"), "lex error at offset 0: bad byte");
    }
}
