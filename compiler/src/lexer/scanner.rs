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
                b'+' => self.push_single(TokenKind::Plus),
                b'-' => {
                    if self.peek_byte(1) == Some(b'>') {
                        self.push_two(TokenKind::Arrow);
                    } else {
                        self.push_single(TokenKind::Minus);
                    }
                }
                b'*' => self.push_single(TokenKind::Star),
                b'/' => self.push_single(TokenKind::Slash),
                b'^' => self.push_single(TokenKind::Caret),
                b'=' => {
                    if self.peek_byte(1) == Some(b'=') {
                        self.push_two(TokenKind::EqEq);
                    } else {
                        self.push_single(TokenKind::Eq);
                    }
                }
                b'!' => {
                    if self.peek_byte(1) == Some(b'=') {
                        self.push_two(TokenKind::Neq);
                    } else {
                        return Err(CompileError::lex(
                            Span::new(self.pos, self.pos + 1),
                            "unexpected '!' (did you mean '!='?)",
                        ));
                    }
                }
                b'<' => {
                    if self.peek_byte(1) == Some(b'=') {
                        self.push_two(TokenKind::Le);
                    } else {
                        self.push_single(TokenKind::Lt);
                    }
                }
                b'>' => {
                    if self.peek_byte(1) == Some(b'=') {
                        self.push_two(TokenKind::Ge);
                    } else {
                        self.push_single(TokenKind::Gt);
                    }
                }
                b'(' => self.push_single(TokenKind::LParen),
                b')' => self.push_single(TokenKind::RParen),
                b'[' => self.push_single(TokenKind::LBracket),
                b']' => self.push_single(TokenKind::RBracket),
                b'{' => self.push_single(TokenKind::LBrace),
                b'}' => self.push_single(TokenKind::RBrace),
                b':' => self.push_single(TokenKind::Colon),
                b',' => self.push_single(TokenKind::Comma),
                b'.' => self.push_single(TokenKind::Dot),
                b'0'..=b'9' => self.scan_number()?,
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
        if let Some(Token { kind: TokenKind::Newline, .. }) = self.tokens.last() {
            return;
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

    fn push_single(&mut self, kind: TokenKind) {
        let start = self.pos;
        self.pos += 1;
        self.tokens.push(Token {
            kind,
            span: Span::new(start, start + 1),
        });
    }

    fn push_two(&mut self, kind: TokenKind) {
        let start = self.pos;
        self.pos += 2;
        self.tokens.push(Token {
            kind,
            span: Span::new(start, start + 2),
        });
    }

    fn scan_number(&mut self) -> Result<(), CompileError> {
        let start = self.pos;
        while self.pos < self.source.len() && self.source[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        let mut is_float = false;

        // Fractional part: require digit on both sides of '.'.
        if self.peek_byte(0) == Some(b'.') {
            if let Some(next) = self.peek_byte(1) {
                if next.is_ascii_digit() {
                    is_float = true;
                    self.pos += 1;
                    while self.pos < self.source.len()
                        && self.source[self.pos].is_ascii_digit()
                    {
                        self.pos += 1;
                    }
                } else {
                    return Err(CompileError::lex(
                        Span::new(self.pos, self.pos + 1),
                        "expected digit after '.' in float literal",
                    ));
                }
            } else {
                return Err(CompileError::lex(
                    Span::new(self.pos, self.pos + 1),
                    "expected digit after '.' in float literal",
                ));
            }
        }

        // Exponent part.
        if matches!(self.peek_byte(0), Some(b'e') | Some(b'E')) {
            is_float = true;
            self.pos += 1;
            if matches!(self.peek_byte(0), Some(b'+') | Some(b'-')) {
                self.pos += 1;
            }
            let exp_start = self.pos;
            while self.pos < self.source.len() && self.source[self.pos].is_ascii_digit() {
                self.pos += 1;
            }
            if self.pos == exp_start {
                return Err(CompileError::lex(
                    Span::new(self.pos, self.pos + 1),
                    "expected digits in exponent",
                ));
            }
        }

        let span = Span::new(start, self.pos);
        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();
        let kind = if is_float {
            TokenKind::Float(text.parse::<f64>().map_err(|e| {
                CompileError::lex(span, format!("invalid float literal: {e}"))
            })?)
        } else {
            TokenKind::Int(text.parse::<i64>().map_err(|e| {
                CompileError::lex(span, format!("invalid int literal: {e}"))
            })?)
        };
        self.tokens.push(Token { kind, span });
        Ok(())
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

    #[test]
    fn single_char_operators() {
        assert_eq!(
            kinds("+ - * / ^"),
            vec![
                TokenKind::Plus, TokenKind::Minus, TokenKind::Star,
                TokenKind::Slash, TokenKind::Caret, TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn comparison_operators() {
        assert_eq!(
            kinds("= == != < > <= >="),
            vec![
                TokenKind::Eq, TokenKind::EqEq, TokenKind::Neq,
                TokenKind::Lt, TokenKind::Gt, TokenKind::Le, TokenKind::Ge,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn delimiters() {
        assert_eq!(
            kinds("( ) [ ] { } : , ."),
            vec![
                TokenKind::LParen, TokenKind::RParen,
                TokenKind::LBracket, TokenKind::RBracket,
                TokenKind::LBrace, TokenKind::RBrace,
                TokenKind::Colon, TokenKind::Comma, TokenKind::Dot,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn arrow_operator() {
        assert_eq!(
            kinds("-> -"),
            vec![TokenKind::Arrow, TokenKind::Minus, TokenKind::Eof]
        );
    }

    #[test]
    fn integer_literals() {
        assert_eq!(
            kinds("42 0 123456"),
            vec![
                TokenKind::Int(42),
                TokenKind::Int(0),
                TokenKind::Int(123456),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    #[allow(clippy::approx_constant)]
    fn float_literals() {
        let ks = kinds("3.14 0.0 1.5e-10");
        assert_eq!(ks.len(), 4);
        match (&ks[0], &ks[1], &ks[2]) {
            (TokenKind::Float(a), TokenKind::Float(b), TokenKind::Float(c)) => {
                assert!((a - 3.14).abs() < 1e-12);
                assert!((b - 0.0).abs() < 1e-12);
                assert!((c - 1.5e-10).abs() < 1e-20);
            }
            _ => panic!("expected three floats, got {ks:?}"),
        }
    }

    #[test]
    fn trailing_dot_is_error() {
        assert!(tokenize("1.").is_err());
    }
}
