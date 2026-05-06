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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
    Note,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub level: Level,
    pub phase: Phase,
    pub span: Span,
    pub message: String,
    pub labels: Vec<(Span, String)>,
    pub notes: Vec<String>,
}

impl Diagnostic {
    pub fn new(level: Level, phase: Phase, span: Span, message: impl Into<String>) -> Self {
        Self {
            level,
            phase,
            span,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
        }
    }

    pub fn lex_error(span: Span, message: impl Into<String>) -> Self {
        Self::new(Level::Error, Phase::Lex, span, message)
    }

    pub fn parse_error(span: Span, message: impl Into<String>) -> Self {
        Self::new(Level::Error, Phase::Parse, span, message)
    }

    pub fn type_error(span: Span, message: impl Into<String>) -> Self {
        Self::new(Level::Error, Phase::Sema, span, message)
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self::new(Level::Warning, Phase::Sema, span, message)
    }

    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push((span, message.into()));
        self
    }

    pub fn with_note(mut self, message: impl Into<String>) -> Self {
        self.notes.push(message.into());
        self
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

    #[test]
    fn type_error_uses_sema_phase_and_error_level() {
        let d = Diagnostic::type_error(Span::new(0, 1), "type mismatch");
        assert_eq!(d.phase, Phase::Sema);
        assert_eq!(d.level, Level::Error);
        assert_eq!(d.message, "type mismatch");
        assert!(d.labels.is_empty());
        assert!(d.notes.is_empty());
    }

    #[test]
    fn warning_uses_sema_phase_and_warning_level() {
        let d = Diagnostic::warning(Span::new(0, 1), "precision risk");
        assert_eq!(d.phase, Phase::Sema);
        assert_eq!(d.level, Level::Warning);
    }

    #[test]
    fn with_label_appends_to_labels() {
        let d = Diagnostic::type_error(Span::new(0, 1), "expected Int")
            .with_label(Span::new(5, 10), "found String here");
        assert_eq!(d.labels.len(), 1);
        assert_eq!(d.labels[0].1, "found String here");
    }

    #[test]
    fn with_note_appends_to_notes() {
        let d = Diagnostic::type_error(Span::new(0, 1), "type mismatch")
            .with_note("did you mean to_int(x)?")
            .with_note("see docs/types.md for conversion rules");
        assert_eq!(d.notes.len(), 2);
        assert_eq!(d.notes[0], "did you mean to_int(x)?");
    }

    #[test]
    fn lex_error_default_level_is_error() {
        let d = Diagnostic::lex_error(Span::new(0, 1), "bad byte");
        assert_eq!(d.level, Level::Error);
    }

    #[test]
    fn parse_error_default_level_is_error() {
        let d = Diagnostic::parse_error(Span::new(0, 1), "expected ')'");
        assert_eq!(d.level, Level::Error);
    }
}
