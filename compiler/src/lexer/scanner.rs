//! Hand-written lexer state machine.

use crate::error::CompileError;
use crate::lexer::token::{Token, TokenKind};
use crate::source::Span;

pub fn tokenize(source: &str) -> Result<Vec<Token>, CompileError> {
    let mut scanner = Scanner::new(source);
    scanner.run()?;
    Ok(scanner.tokens)
}

struct Scanner<'a> {
    source: &'a [u8],
    pos: usize,
    tokens: Vec<Token>,
}

impl<'a> Scanner<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source: source.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
        }
    }

    fn run(&mut self) -> Result<(), CompileError> {
        while self.pos < self.source.len() {
            let b = self.source[self.pos];
            match b {
                b' ' | b'\t' | b'\r' => {
                    self.pos += 1;
                }
                b'\n' => {
                    let start = self.pos;
                    self.pos += 1;
                    self.push_newline_collapsed(start);
                }
                b'/' if self.peek_byte(1) == Some(b'/') => {
                    self.skip_line_comment();
                }
                _ => {
                    return Err(CompileError::lex(
                        Span::new(self.pos, self.pos + 1),
                        format!("unexpected byte 0x{b:02x}"),
                    ));
                }
            }
        }
        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::new(self.pos, self.pos),
        });
        Ok(())
    }

    fn peek_byte(&self, offset: usize) -> Option<u8> {
        self.source.get(self.pos + offset).copied()
    }

    fn push_newline_collapsed(&mut self, start: usize) {
        // Skip any following whitespace-only lines; collapse consecutive newlines.
        while self.pos < self.source.len() {
            match self.source[self.pos] {
                b' ' | b'\t' | b'\r' => self.pos += 1,
                b'\n' => self.pos += 1,
                _ => break,
            }
        }
        if let Some(last) = self.tokens.last() {
            if matches!(last.kind, TokenKind::Newline) {
                return;
            }
        }
        self.tokens.push(Token {
            kind: TokenKind::Newline,
            span: Span::new(start, start + 1),
        });
    }

    fn skip_line_comment(&mut self) {
        while self.pos < self.source.len() && self.source[self.pos] != b'\n' {
            self.pos += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(source: &str) -> Vec<TokenKind> {
        tokenize(source).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn empty_source() {
        assert_eq!(kinds(""), vec![TokenKind::Eof]);
    }

    #[test]
    fn whitespace_only() {
        assert_eq!(kinds("   \t  "), vec![TokenKind::Eof]);
    }

    #[test]
    fn single_newline() {
        assert_eq!(kinds("\n"), vec![TokenKind::Newline, TokenKind::Eof]);
    }

    #[test]
    fn consecutive_newlines_collapsed() {
        assert_eq!(
            kinds("\n\n\n"),
            vec![TokenKind::Newline, TokenKind::Eof]
        );
    }

    #[test]
    fn line_comment_ignored() {
        assert_eq!(
            kinds("// a comment\n"),
            vec![TokenKind::Newline, TokenKind::Eof]
        );
    }
}
