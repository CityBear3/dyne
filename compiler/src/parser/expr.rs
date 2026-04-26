//! Expression parser.

use crate::ast::{Expr, ExprKind};
use crate::error::CompileError;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::source::Span;

#[allow(dead_code)] // transient until Task 19 wires this into stmt parsing
pub(crate) fn parse_expr(p: &mut Parser) -> Result<Expr, CompileError> {
    parse_bp(p, 0)
}

fn parse_primary(p: &mut Parser) -> Result<Expr, CompileError> {
    let tok = p.peek().clone();
    match &tok.kind {
        TokenKind::Int(n) => {
            p.advance();
            Ok(Expr { kind: ExprKind::IntLit(*n), span: tok.span })
        }
        TokenKind::Float(n) => {
            p.advance();
            Ok(Expr { kind: ExprKind::FloatLit(*n), span: tok.span })
        }
        TokenKind::Str(s) => {
            let s = s.clone();
            p.advance();
            Ok(Expr { kind: ExprKind::StrLit(s), span: tok.span })
        }
        TokenKind::True => {
            p.advance();
            Ok(Expr { kind: ExprKind::BoolLit(true), span: tok.span })
        }
        TokenKind::False => {
            p.advance();
            Ok(Expr { kind: ExprKind::BoolLit(false), span: tok.span })
        }
        TokenKind::Ident(name) => {
            let name = name.clone();
            p.advance();
            Ok(Expr { kind: ExprKind::Ident(name), span: tok.span })
        }
        TokenKind::LParen => {
            p.advance();
            let inner = parse_expr(p)?;
            let end = p.peek().span;
            p.expect(&TokenKind::RParen, "')'")?;
            Ok(Expr {
                kind: inner.kind,
                span: Span::merge(tok.span, end),
            })
        }
        TokenKind::LBracket => parse_vec_or_mat_lit(p),
        _ => Err(CompileError::parse(
            tok.span,
            format!("expected expression, found {:?}", tok.kind),
        )),
    }
}

fn parse_vec_or_mat_lit(p: &mut Parser) -> Result<Expr, CompileError> {
    let start = p.peek().span;
    p.advance(); // consume '['
    // Matrix if first element is '['
    if p.at(&TokenKind::LBracket) {
        let mut rows = Vec::new();
        rows.push(parse_row(p)?);
        while p.eat(&TokenKind::Comma) {
            rows.push(parse_row(p)?);
        }
        let end = p.peek().span;
        p.expect(&TokenKind::RBracket, "']'")?;
        return Ok(Expr {
            kind: ExprKind::MatLit(rows),
            span: Span::merge(start, end),
        });
    }
    // Vector literal (possibly empty)
    let mut elems = Vec::new();
    if !p.at(&TokenKind::RBracket) {
        elems.push(parse_expr(p)?);
        while p.eat(&TokenKind::Comma) {
            elems.push(parse_expr(p)?);
        }
    }
    let end = p.peek().span;
    p.expect(&TokenKind::RBracket, "']'")?;
    Ok(Expr {
        kind: ExprKind::VecLit(elems),
        span: Span::merge(start, end),
    })
}

fn parse_row(p: &mut Parser) -> Result<Vec<Expr>, CompileError> {
    p.expect(&TokenKind::LBracket, "'['")?;
    let mut row = Vec::new();
    if !p.at(&TokenKind::RBracket) {
        row.push(parse_expr(p)?);
        while p.eat(&TokenKind::Comma) {
            row.push(parse_expr(p)?);
        }
    }
    p.expect(&TokenKind::RBracket, "']'")?;
    Ok(row)
}

// Placeholder Pratt parser — binding powers added in Task 17.
fn parse_bp(p: &mut Parser, _min_bp: u8) -> Result<Expr, CompileError> {
    parse_primary(p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::tokenize;

    fn parse(source: &str) -> Expr {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        parse_expr(&mut p).unwrap()
    }

    #[test]
    fn int_literal() {
        assert_eq!(parse("42").kind, ExprKind::IntLit(42));
    }

    #[test]
    fn float_literal() {
        assert!(matches!(parse("3.14").kind, ExprKind::FloatLit(_)));
    }

    #[test]
    fn string_literal() {
        assert_eq!(
            parse(r#""hello""#).kind,
            ExprKind::StrLit("hello".into())
        );
    }

    #[test]
    fn bool_literals() {
        assert_eq!(parse("true").kind, ExprKind::BoolLit(true));
        assert_eq!(parse("false").kind, ExprKind::BoolLit(false));
    }

    #[test]
    fn identifier() {
        assert_eq!(parse("x").kind, ExprKind::Ident("x".into()));
    }

    #[test]
    fn parenthesized() {
        assert_eq!(parse("(42)").kind, ExprKind::IntLit(42));
    }

    #[test]
    fn vector_literal() {
        match parse("[1.0, 2.0, 3.0]").kind {
            ExprKind::VecLit(v) => assert_eq!(v.len(), 3),
            _ => panic!("expected VecLit"),
        }
    }

    #[test]
    fn matrix_literal() {
        match parse("[[1.0, 0.0], [0.0, 1.0]]").kind {
            ExprKind::MatLit(m) => {
                assert_eq!(m.len(), 2);
                assert_eq!(m[0].len(), 2);
            }
            _ => panic!("expected MatLit"),
        }
    }
}
