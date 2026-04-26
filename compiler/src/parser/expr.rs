//! Expression parser.

use crate::ast::{BinOp, Expr, ExprKind, UnaryOp};
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

fn parse_postfix(p: &mut Parser) -> Result<Expr, CompileError> {
    let mut expr = parse_primary(p)?;
    loop {
        match p.peek_kind() {
            TokenKind::LParen => {
                p.advance();
                let mut args = Vec::new();
                if !p.at(&TokenKind::RParen) {
                    args.push(parse_expr(p)?);
                    while p.eat(&TokenKind::Comma) {
                        args.push(parse_expr(p)?);
                    }
                }
                let end = p.peek().span;
                p.expect(&TokenKind::RParen, "')'")?;
                let span = Span::merge(expr.span, end);
                expr = Expr {
                    kind: ExprKind::Call(Box::new(expr), args),
                    span,
                };
            }
            TokenKind::LBracket => {
                p.advance();
                let idx = parse_expr(p)?;
                let end = p.peek().span;
                p.expect(&TokenKind::RBracket, "']'")?;
                let span = Span::merge(expr.span, end);
                expr = Expr {
                    kind: ExprKind::Index(Box::new(expr), Box::new(idx)),
                    span,
                };
            }
            TokenKind::Dot => {
                p.advance();
                let field_tok = p.peek().clone();
                let field = match &field_tok.kind {
                    TokenKind::Ident(n) => n.clone(),
                    _ => {
                        return Err(CompileError::parse(
                            field_tok.span,
                            format!("expected field name, found {:?}", field_tok.kind),
                        ));
                    }
                };
                p.advance();
                let span = Span::merge(expr.span, field_tok.span);
                expr = Expr {
                    kind: ExprKind::FieldAccess(Box::new(expr), field),
                    span,
                };
            }
            _ => break,
        }
    }
    Ok(expr)
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

fn parse_bp(p: &mut Parser, min_bp: u8) -> Result<Expr, CompileError> {
    let mut lhs = parse_unary(p)?;

    while let Some((op, lbp, rbp)) = infix_op(p.peek_kind()) {
        if lbp < min_bp {
            break;
        }
        p.advance();
        let rhs = parse_bp(p, rbp)?;
        let span = Span::merge(lhs.span, rhs.span);
        lhs = Expr {
            kind: ExprKind::BinOp(op, Box::new(lhs), Box::new(rhs)),
            span,
        };
    }

    Ok(lhs)
}

fn parse_unary(p: &mut Parser) -> Result<Expr, CompileError> {
    let tok = p.peek().clone();
    match tok.kind {
        TokenKind::Minus => {
            p.advance();
            let rhs = parse_unary(p)?;
            let span = Span::merge(tok.span, rhs.span);
            Ok(Expr {
                kind: ExprKind::UnaryOp(UnaryOp::Neg, Box::new(rhs)),
                span,
            })
        }
        TokenKind::Not => {
            p.advance();
            let rhs = parse_unary(p)?;
            let span = Span::merge(tok.span, rhs.span);
            Ok(Expr {
                kind: ExprKind::UnaryOp(UnaryOp::Not, Box::new(rhs)),
                span,
            })
        }
        _ => parse_postfix(p),
    }
}

/// Returns (op, left bp, right bp). Right bp > left bp => right-associative.
fn infix_op(kind: &TokenKind) -> Option<(BinOp, u8, u8)> {
    Some(match kind {
        TokenKind::Or => (BinOp::Or, 1, 2),
        TokenKind::And => (BinOp::And, 3, 4),
        TokenKind::EqEq => (BinOp::Eq, 5, 6),
        TokenKind::Neq => (BinOp::Neq, 5, 6),
        TokenKind::Lt => (BinOp::Lt, 5, 6),
        TokenKind::Gt => (BinOp::Gt, 5, 6),
        TokenKind::Le => (BinOp::Le, 5, 6),
        TokenKind::Ge => (BinOp::Ge, 5, 6),
        TokenKind::Plus => (BinOp::Add, 7, 8),
        TokenKind::Minus => (BinOp::Sub, 7, 8),
        TokenKind::Star => (BinOp::Mul, 9, 10),
        TokenKind::Slash => (BinOp::Div, 9, 10),
        TokenKind::Caret => (BinOp::Pow, 12, 11), // right-associative
        _ => return None,
    })
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

    #[test]
    fn addition() {
        let e = parse("1 + 2");
        match e.kind {
            ExprKind::BinOp(BinOp::Add, _, _) => {}
            _ => panic!("expected Add"),
        }
    }

    #[test]
    fn precedence_mul_over_add() {
        // 1 + 2 * 3 => Add(1, Mul(2, 3))
        let e = parse("1 + 2 * 3");
        match e.kind {
            ExprKind::BinOp(BinOp::Add, lhs, rhs) => {
                assert_eq!(lhs.kind, ExprKind::IntLit(1));
                match rhs.kind {
                    ExprKind::BinOp(BinOp::Mul, _, _) => {}
                    _ => panic!("expected Mul on right"),
                }
            }
            _ => panic!("expected Add at root"),
        }
    }

    #[test]
    fn pow_right_associative() {
        // 2 ^ 3 ^ 2 => Pow(2, Pow(3, 2))
        let e = parse("2 ^ 3 ^ 2");
        match e.kind {
            ExprKind::BinOp(BinOp::Pow, lhs, rhs) => {
                assert_eq!(lhs.kind, ExprKind::IntLit(2));
                match rhs.kind {
                    ExprKind::BinOp(BinOp::Pow, _, _) => {}
                    _ => panic!("expected nested Pow on right"),
                }
            }
            _ => panic!("expected Pow at root"),
        }
    }

    #[test]
    fn unary_neg() {
        let e = parse("-x");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Neg, _) => {}
            _ => panic!("expected Neg"),
        }
    }

    #[test]
    fn unary_not() {
        let e = parse("not true");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Not, _) => {}
            _ => panic!("expected Not"),
        }
    }

    #[test]
    fn logical_precedence() {
        // a and b or c => Or(And(a, b), c)
        let e = parse("a and b or c");
        match e.kind {
            ExprKind::BinOp(BinOp::Or, lhs, _) => match lhs.kind {
                ExprKind::BinOp(BinOp::And, _, _) => {}
                _ => panic!("expected And inside Or"),
            },
            _ => panic!("expected Or at root"),
        }
    }

    #[test]
    fn function_call() {
        let e = parse("f(1, 2)");
        match e.kind {
            ExprKind::Call(callee, args) => {
                assert_eq!(callee.kind, ExprKind::Ident("f".into()));
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn indexing() {
        let e = parse("a[0]");
        match e.kind {
            ExprKind::Index(obj, idx) => {
                assert_eq!(obj.kind, ExprKind::Ident("a".into()));
                assert_eq!(idx.kind, ExprKind::IntLit(0));
            }
            _ => panic!("expected Index"),
        }
    }

    #[test]
    fn field_access() {
        let e = parse("p.q");
        match e.kind {
            ExprKind::FieldAccess(obj, field) => {
                assert_eq!(obj.kind, ExprKind::Ident("p".into()));
                assert_eq!(field, "q");
            }
            _ => panic!("expected FieldAccess"),
        }
    }

    #[test]
    fn chained_postfix() {
        // a.b[0](x)
        let e = parse("a.b[0](x)");
        if let ExprKind::Call(callee, _) = e.kind
            && let ExprKind::Index(obj, _) = callee.kind
            && let ExprKind::FieldAccess(inner, field) = obj.kind
        {
            assert_eq!(inner.kind, ExprKind::Ident("a".into()));
            assert_eq!(field, "b");
            return;
        }
        panic!("chained postfix structure mismatch");
    }
}
