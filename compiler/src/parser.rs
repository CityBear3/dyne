//! Syntax analyzer.

pub mod types;
pub mod expr;
pub mod stmt;

use crate::ast::Program;
use crate::error::CompileError;
use crate::lexer::{Token, TokenKind};
use crate::source::Span;

pub fn parse(tokens: Vec<Token>) -> Result<Program, CompileError> {
    let mut parser = Parser::new(&tokens);
    stmt::parse_program(&mut parser)
}

pub(crate) struct Parser<'t> {
    tokens: &'t [Token],
    pos: usize,
}

#[allow(dead_code)]
impl<'t> Parser<'t> {
    pub fn new(tokens: &'t [Token]) -> Self {
        Self { tokens, pos: 0 }
    }

    pub fn peek(&self) -> &'t Token {
        &self.tokens[self.pos.min(self.tokens.len().saturating_sub(1))]
    }

    pub fn peek_kind(&self) -> &'t TokenKind {
        &self.peek().kind
    }

    pub fn peek_ahead(&self, offset: usize) -> &'t TokenKind {
        let idx = (self.pos + offset).min(self.tokens.len().saturating_sub(1));
        &self.tokens[idx].kind
    }

    pub fn advance(&mut self) -> &'t Token {
        let tok = &self.tokens[self.pos.min(self.tokens.len().saturating_sub(1))];
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    pub fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.peek_kind()) == std::mem::discriminant(kind)
    }

    pub fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub fn expect(&mut self, kind: &TokenKind, ctx: &str) -> Result<&'t Token, CompileError> {
        if self.at(kind) {
            Ok(self.advance())
        } else {
            let tok = self.peek();
            Err(CompileError::parse(
                tok.span,
                format!("expected {ctx}, found {:?}", tok.kind),
            ))
        }
    }

    pub fn consume_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.advance();
        }
    }

    pub fn current_span(&self) -> Span {
        self.peek().span
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::tokenize;

    #[test]
    fn peek_and_advance() {
        let toks = tokenize("let x").unwrap();
        let mut p = Parser::new(&toks);
        assert!(matches!(p.peek_kind(), TokenKind::Let));
        p.advance();
        assert!(matches!(p.peek_kind(), TokenKind::Ident(n) if n == "x"));
    }

    #[test]
    fn expect_error_message() {
        let toks = tokenize("let").unwrap();
        let mut p = Parser::new(&toks);
        p.advance();
        let err = p.expect(&TokenKind::Eq, "'='").unwrap_err();
        assert!(err.message.contains("expected '='"));
    }

    #[test]
    fn consume_newlines_skips() {
        let toks = tokenize("\n\nlet").unwrap();
        let mut p = Parser::new(&toks);
        p.consume_newlines();
        assert!(matches!(p.peek_kind(), TokenKind::Let));
    }
}
