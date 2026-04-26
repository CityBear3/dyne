//! Source file and span utilities.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(a: Span, b: Span) -> Span {
        Span {
            start: a.start.min(b.start),
            end: a.end.max(b.end),
        }
    }
}

#[derive(Debug)]
pub struct SourceFile {
    text: String,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn new(text: impl Into<String>) -> Self {
        let text = text.into();
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self { text, line_starts }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    /// Returns (line, column) as 1-based indices for the given byte offset.
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let line_idx = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let line_start = self.line_starts[line_idx];
        (line_idx + 1, offset - line_start + 1)
    }

    /// Returns the full text of the given 1-based line number.
    pub fn line_text(&self, line: usize) -> Option<&str> {
        let start = *self.line_starts.get(line - 1)?;
        let end = self
            .line_starts
            .get(line)
            .copied()
            .unwrap_or(self.text.len());
        let s = &self.text[start..end];
        Some(s.trim_end_matches('\n').trim_end_matches('\r'))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_merge() {
        let a = Span::new(0, 3);
        let b = Span::new(2, 5);
        assert_eq!(Span::merge(a, b), Span::new(0, 5));
    }

    #[test]
    fn line_col_single_line() {
        let src = SourceFile::new("abcde");
        assert_eq!(src.line_col(0), (1, 1));
        assert_eq!(src.line_col(3), (1, 4));
    }

    #[test]
    fn line_col_multi_line() {
        let src = SourceFile::new("ab\ncd\nef");
        assert_eq!(src.line_col(0), (1, 1));
        assert_eq!(src.line_col(3), (2, 1));
        assert_eq!(src.line_col(4), (2, 2));
        assert_eq!(src.line_col(6), (3, 1));
    }

    #[test]
    fn line_text_fetch() {
        let src = SourceFile::new("foo\nbar\nbaz");
        assert_eq!(src.line_text(1), Some("foo"));
        assert_eq!(src.line_text(2), Some("bar"));
        assert_eq!(src.line_text(3), Some("baz"));
        assert_eq!(src.line_text(4), None);
    }
}
