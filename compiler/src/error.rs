//! Compile-time error type.

use crate::source::{SourceFile, Span};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    Lex,
    Parse,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CompileError {
    pub kind: ErrorKind,
    pub span: Span,
    pub message: String,
}

impl CompileError {
    pub fn new(kind: ErrorKind, span: Span, message: impl Into<String>) -> Self {
        Self {
            kind,
            span,
            message: message.into(),
        }
    }

    pub fn lex(span: Span, message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Lex, span, message)
    }

    pub fn parse(span: Span, message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Parse, span, message)
    }

    /// Render the error with line/column and source excerpt.
    pub fn render(&self, source: &SourceFile) -> String {
        let (line, col) = source.line_col(self.span.start);
        let kind = match self.kind {
            ErrorKind::Lex => "lex error",
            ErrorKind::Parse => "parse error",
        };
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

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            ErrorKind::Lex => "lex error",
            ErrorKind::Parse => "parse error",
        };
        write!(
            f,
            "{kind} at offset {}: {}",
            self.span.start, self.message
        )
    }
}

impl std::error::Error for CompileError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_points_to_line_and_column() {
        let src = SourceFile::new("let x = 1\nlet y = ?\nlet z = 3");
        let err = CompileError::lex(Span::new(18, 19), "unexpected character '?'");
        let rendered = err.render(&src);
        assert!(rendered.contains("line 2, col 9"));
        assert!(rendered.contains("let y = ?"));
        assert!(rendered.contains("unexpected character '?'"));
    }

    #[test]
    fn display_short_form() {
        let err = CompileError::parse(Span::new(5, 6), "expected ')'");
        assert_eq!(
            format!("{err}"),
            "parse error at offset 5: expected ')'"
        );
    }
}
