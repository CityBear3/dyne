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

    fn name(self) -> &'static str {
        match self {
            Phase::Lex => "lex",
            Phase::Parse => "parse",
            Phase::Sema => "sema",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
    Note,
}

impl Level {
    fn name(self) -> &'static str {
        match self {
            Level::Error => "error",
            Level::Warning => "warning",
            Level::Note => "note",
        }
    }
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

    /// Render the diagnostic in rustc style: a `{level}[{phase}]:` header,
    /// an arrow line locating the primary span, a line-number gutter with
    /// the source excerpt and a `^` underline for the primary span, one
    /// `-` underline row per label (label text appended; the label's line
    /// is re-echoed only when it differs from the previously echoed line),
    /// and trailing `= note:` lines. Every span the diagnostic carries is
    /// visible. Spans crossing a line boundary are clamped to their first
    /// line by `SourceFile::line_col_width`.
    pub fn render(&self, source: &SourceFile) -> String {
        let (line, col, width) = source.line_col_width(self.span);

        // Primary row first, then label rows in emission order.
        let mut rows: Vec<(usize, usize, usize, char, Option<&str>)> =
            vec![(line, col, width, '^', None)];
        for (span, text) in &self.labels {
            // A label span can originate in a different source (e.g. a
            // builtins.dy span on `duplicate_name` when user code redefines
            // a built-in name); rendering it against this source would point
            // at a nonexistent location. Skip such rows — the primary span
            // and message still identify the diagnostic. A span that is
            // out-of-source but numerically in range cannot be detected
            // until Span carries a source id (deferred design).
            if span.start >= source.text().len() {
                continue;
            }
            let (l, c, w) = source.line_col_width(*span);
            rows.push((l, c, w, '-', Some(text)));
        }

        let gutter = rows
            .iter()
            .map(|r| r.0.to_string().len())
            .max()
            .unwrap_or(1);
        let pad = " ".repeat(gutter);

        let mut out = format!(
            "{}[{}]: {}\n  --> line {line}, col {col}\n{pad} |\n",
            self.level.name(),
            self.phase.name(),
            self.message,
        );
        let mut echoed = 0; // 0 = nothing echoed yet (line numbers are 1-based)
        for (l, c, w, marker, text) in rows {
            if l != echoed {
                let excerpt = source.line_text(l).unwrap_or("");
                out.push_str(&format!("{l:>gutter$} | {excerpt}\n"));
                echoed = l;
            }
            out.push_str(&format!(
                "{pad} | {}{}",
                " ".repeat(c - 1),
                marker.to_string().repeat(w)
            ));
            if let Some(t) = text {
                out.push(' ');
                out.push_str(t);
            }
            out.push('\n');
        }
        for note in &self.notes {
            out.push_str(&format!("{pad} = note: {note}\n"));
        }
        out.pop(); // no trailing newline
        out
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
    fn render_primary_span_rustc_style() {
        let src = SourceFile::new("let x = 1\nlet y = ?\nlet z = 3");
        let err = Diagnostic::lex_error(Span::new(18, 19), "unexpected character '?'");
        assert_eq!(
            err.render(&src),
            "error[lex]: unexpected character '?'\n  --> line 2, col 9\n  |\n2 | let y = ?\n  |         ^"
        );
    }

    #[test]
    fn render_two_labels_same_line() {
        let src = SourceFile::new("return a + b");
        let err = Diagnostic::type_error(Span::new(7, 12), "dimension mismatch in '+'")
            .with_label(Span::new(7, 8), "left side has Scalar<kg>")
            .with_label(Span::new(11, 12), "right side has Scalar<m>");
        assert_eq!(
            err.render(&src),
            "error[sema]: dimension mismatch in '+'\n  --> line 1, col 8\n  |\n1 | return a + b\n  |        ^^^^^\n  |        - left side has Scalar<kg>\n  |            - right side has Scalar<m>"
        );
    }

    #[test]
    fn render_label_on_other_line_echoes_that_line() {
        let src = SourceFile::new("let a = 1\nlet a = 2");
        let err = Diagnostic::type_error(Span::new(14, 15), "`a` is already defined in this scope")
            .with_label(Span::new(4, 5), "previously defined here");
        assert_eq!(
            err.render(&src),
            "error[sema]: `a` is already defined in this scope\n  --> line 2, col 5\n  |\n2 | let a = 2\n  |     ^\n1 | let a = 1\n  |     - previously defined here"
        );
    }

    #[test]
    fn render_notes_as_trailing_lines() {
        let src = SourceFile::new("let x = y");
        let err = Diagnostic::type_error(Span::new(8, 9), "type mismatch")
            .with_note("did you mean to_int(x)?");
        assert_eq!(
            err.render(&src),
            "error[sema]: type mismatch\n  --> line 1, col 9\n  |\n1 | let x = y\n  |         ^\n  = note: did you mean to_int(x)?"
        );
    }

    #[test]
    fn render_warning_prefix() {
        let src = SourceFile::new("x = x + 1.5");
        let w = Diagnostic::warning(Span::new(4, 11), "precision risk");
        assert!(w.render(&src).starts_with("warning[sema]: precision risk"));
    }

    #[test]
    fn render_multi_digit_gutter_right_aligns() {
        // Primary on line 10, a label back on line 9: the gutter is 2 wide,
        // so the single-digit line echoes right-aligned (` 9 |`) and every
        // separator/underline row uses a 2-space pad.
        let src = SourceFile::new("a\nb\nc\nd\ne\nf\ng\nh\nlet a = 1\nlet a = 2");
        let err = Diagnostic::type_error(Span::new(30, 31), "`a` is already defined in this scope")
            .with_label(Span::new(20, 21), "previously defined here");
        assert_eq!(
            err.render(&src),
            "error[sema]: `a` is already defined in this scope\n  --> line 10, col 5\n   |\n10 | let a = 2\n   |     ^\n 9 | let a = 1\n   |     - previously defined here"
        );
    }

    #[test]
    fn render_skips_label_beyond_source_end() {
        let src = SourceFile::new("let a = 1");
        let err = Diagnostic::type_error(Span::new(4, 5), "`a` is already defined in this scope")
            .with_label(Span::new(500, 506), "previously defined here");
        let rendered = err.render(&src);
        // The out-of-range label row is skipped entirely; primary still renders.
        assert!(
            !rendered.contains("previously defined here"),
            "rendered: {rendered}"
        );
        assert!(rendered.contains("let a = 1"));
        assert!(rendered.contains('^'));
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
        assert!(rendered.starts_with("error[parse]: expected '('"));
        assert!(rendered.contains("ab cd"));
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
        assert_eq!(d.labels[0].0, Span::new(5, 10));
        assert_eq!(d.labels[0].1, "found String here");
    }

    #[test]
    fn with_note_appends_to_notes() {
        let d = Diagnostic::type_error(Span::new(0, 1), "type mismatch")
            .with_note("did you mean to_int(x)?")
            .with_note("see docs/types.md for conversion rules");
        assert_eq!(d.notes.len(), 2);
        assert_eq!(d.notes[0], "did you mean to_int(x)?");
        assert_eq!(d.notes[1], "see docs/types.md for conversion rules");
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
