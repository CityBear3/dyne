//! Syntax analyzer.

pub(crate) mod expr;
pub(crate) mod stmt;
pub(crate) mod types;

use crate::ast::Program;
use crate::diag::Diagnostic;
use crate::ids::NodeId;
use crate::lexer::{Token, TokenKind};
use crate::source::Span;

/// Parse without a NodeId offset. Reserved for in-crate unit tests that
/// don't need to merge with built-ins; production callers go through
/// `parse_with_node_offset` via `lib::compile`.
#[cfg(test)]
pub(crate) fn parse(tokens: Vec<Token>) -> Result<Program, Diagnostic> {
    parse_with_node_offset(tokens, 0).map(|(p, _)| p)
}

/// Parse with a starting `NodeId` offset and return the parsed `Program`
/// alongside the next `NodeId` that would have been allocated. Used by
/// `compile()` to keep built-in and user-source NodeIds disjoint so the
/// merged `Program` has unique ids per node.
pub(crate) fn parse_with_node_offset(
    tokens: Vec<Token>,
    node_offset: u32,
) -> Result<(Program, u32), Diagnostic> {
    let mut parser = Parser::new_with_offset(&tokens, node_offset);
    let program = stmt::parse_program(&mut parser)?;
    Ok((program, parser.next_node_id))
}

pub(crate) struct Parser<'t> {
    tokens: &'t [Token],
    pos: usize,
    next_node_id: u32,
}

impl<'t> Parser<'t> {
    #[cfg(test)]
    pub(crate) fn new(tokens: &'t [Token]) -> Self {
        Self::new_with_offset(tokens, 0)
    }

    fn new_with_offset(tokens: &'t [Token], offset: u32) -> Self {
        Self {
            tokens,
            pos: 0,
            next_node_id: offset,
        }
    }

    pub(crate) fn fresh_node_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    pub(crate) fn peek(&self) -> &'t Token {
        &self.tokens[self.pos.min(self.tokens.len().saturating_sub(1))]
    }

    pub(crate) fn peek_kind(&self) -> &'t TokenKind {
        &self.peek().kind
    }

    pub(crate) fn peek_ahead(&self, offset: usize) -> &'t TokenKind {
        let idx = (self.pos + offset).min(self.tokens.len().saturating_sub(1));
        &self.tokens[idx].kind
    }

    pub(crate) fn advance(&mut self) -> &'t Token {
        let tok = &self.tokens[self.pos.min(self.tokens.len().saturating_sub(1))];
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    pub(crate) fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.peek_kind()) == std::mem::discriminant(kind)
    }

    pub(crate) fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub(crate) fn expect(&mut self, kind: &TokenKind, ctx: &str) -> Result<&'t Token, Diagnostic> {
        if self.at(kind) {
            Ok(self.advance())
        } else {
            let tok = self.peek();
            Err(Diagnostic::parse_error(
                tok.span,
                format!("expected {ctx}, found {:?}", tok.kind),
            ))
        }
    }

    pub(crate) fn consume_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.advance();
        }
    }

    pub(crate) fn current_span(&self) -> Span {
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
