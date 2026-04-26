//! Expression parser.

use crate::ast::{BinOp, Expr, ExprKind, UnaryOp};
use crate::error::CompileError;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::source::Span;

pub(crate) fn parse_expr(p: &mut Parser) -> Result<Expr, CompileError> {
    parse_bp(p, 0)
}

fn parse_primary(p: &mut Parser) -> Result<Expr, CompileError> {
    let tok = p.peek().clone();
    match &tok.kind {
        TokenKind::Int(n) => {
            p.advance();
            Ok(Expr {
                kind: ExprKind::IntLit(*n),
                span: tok.span,
            })
        }
        TokenKind::Float(n) => {
            p.advance();
            Ok(Expr {
                kind: ExprKind::FloatLit(*n),
                span: tok.span,
            })
        }
        TokenKind::Str(s) => {
            let s = s.clone();
            p.advance();
            Ok(Expr {
                kind: ExprKind::StrLit(s),
                span: tok.span,
            })
        }
        TokenKind::True => {
            p.advance();
            Ok(Expr {
                kind: ExprKind::BoolLit(true),
                span: tok.span,
            })
        }
        TokenKind::False => {
            p.advance();
            Ok(Expr {
                kind: ExprKind::BoolLit(false),
                span: tok.span,
            })
        }
        TokenKind::Ident(name) => {
            let name = name.clone();
            p.advance();
            Ok(Expr {
                kind: ExprKind::Ident(name),
                span: tok.span,
            })
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
        TokenKind::If => parse_if_expr(p),
        _ => Err(CompileError::parse(
            tok.span,
            format!("expected expression, found {:?}", tok.kind),
        )),
    }
}

fn parse_vec_or_mat_lit(p: &mut Parser) -> Result<Expr, CompileError> {
    let start = p.peek().span;
    p.advance(); // consume '['
    p.consume_newlines();
    // Matrix if first element is '['
    if p.at(&TokenKind::LBracket) {
        let mut rows = Vec::new();
        rows.push(parse_row(p)?);
        p.consume_newlines();
        while p.eat(&TokenKind::Comma) {
            p.consume_newlines();
            if p.at(&TokenKind::RBracket) {
                break; // trailing comma
            }
            rows.push(parse_row(p)?);
            p.consume_newlines();
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
        p.consume_newlines();
        while p.eat(&TokenKind::Comma) {
            p.consume_newlines();
            if p.at(&TokenKind::RBracket) {
                break; // trailing comma
            }
            elems.push(parse_expr(p)?);
            p.consume_newlines();
        }
    }
    let end = p.peek().span;
    p.expect(&TokenKind::RBracket, "']'")?;
    Ok(Expr {
        kind: ExprKind::VecLit(elems),
        span: Span::merge(start, end),
    })
}

fn parse_if_expr(p: &mut Parser) -> Result<Expr, CompileError> {
    use crate::ast::IfExpr;
    use crate::parser::stmt::{TokenKindKind, parse_block_until};

    let start = p.current_span();
    p.expect(&TokenKind::If, "'if'")?;
    let cond = parse_expr(p)?;
    p.expect(&TokenKind::Then, "'then'")?;
    let then_block = parse_block_until(
        p,
        &[
            TokenKindKind::Elseif,
            TokenKindKind::Else,
            TokenKindKind::End,
        ],
    )?;

    let mut elseifs = Vec::new();
    while matches!(p.peek_kind(), TokenKind::Elseif) {
        p.advance();
        let cond_i = parse_expr(p)?;
        p.expect(&TokenKind::Then, "'then'")?;
        let block_i = parse_block_until(
            p,
            &[
                TokenKindKind::Elseif,
                TokenKindKind::Else,
                TokenKindKind::End,
            ],
        )?;
        elseifs.push((cond_i, block_i));
    }

    let else_block = if matches!(p.peek_kind(), TokenKind::Else) {
        p.advance();
        Some(parse_block_until(p, &[TokenKindKind::End])?)
    } else {
        None
    };

    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(Expr {
        kind: ExprKind::If(IfExpr {
            cond: Box::new(cond),
            then_block,
            elseifs,
            else_block,
        }),
        span: Span::merge(start, end),
    })
}

fn parse_postfix(p: &mut Parser) -> Result<Expr, CompileError> {
    let mut expr = parse_primary(p)?;
    loop {
        match p.peek_kind() {
            TokenKind::LParen => {
                p.advance();
                p.consume_newlines();
                let mut args = Vec::new();
                if !p.at(&TokenKind::RParen) {
                    args.push(parse_expr(p)?);
                    p.consume_newlines();
                    while p.eat(&TokenKind::Comma) {
                        p.consume_newlines();
                        if p.at(&TokenKind::RParen) {
                            break; // trailing comma
                        }
                        args.push(parse_expr(p)?);
                        p.consume_newlines();
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
    p.consume_newlines();
    let mut row = Vec::new();
    if !p.at(&TokenKind::RBracket) {
        row.push(parse_expr(p)?);
        p.consume_newlines();
        while p.eat(&TokenKind::Comma) {
            p.consume_newlines();
            if p.at(&TokenKind::RBracket) {
                break; // trailing comma
            }
            row.push(parse_expr(p)?);
            p.consume_newlines();
        }
    }
    p.expect(&TokenKind::RBracket, "']'")?;
    Ok(row)
}

fn parse_bp(p: &mut Parser, min_bp: u8) -> Result<Expr, CompileError> {
    let mut lhs = parse_prefix(p)?;

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

/// Prefix operators (`not`, unary `-`) per Design Doc §6.6 precedence table.
/// `not` (precedence 3) consumes comparison and above (rbp = 4).
/// Unary `-` (precedence 7) consumes `^` but stops at `*` `/` (rbp = `^` lbp = 12).
fn parse_prefix(p: &mut Parser) -> Result<Expr, CompileError> {
    let start = p.current_span();
    match p.peek_kind() {
        TokenKind::Not => {
            p.advance();
            let rhs = parse_bp(p, 4)?;
            let span = Span::merge(start, rhs.span);
            Ok(Expr {
                kind: ExprKind::UnaryOp(UnaryOp::Not, Box::new(rhs)),
                span,
            })
        }
        TokenKind::Minus => {
            p.advance();
            let rhs = parse_bp(p, 12)?;
            let span = Span::merge(start, rhs.span);
            Ok(Expr {
                kind: ExprKind::UnaryOp(UnaryOp::Neg, Box::new(rhs)),
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

use crate::ast::{Pattern, PatternKind};

const FLOAT_PATTERN_REJECTED: &str = "floating-point literal patterns are not supported because NaN \u{2260} NaN and rounding error makes equality matches unreliable; use a guard such as `if abs(x - 0.5) < eps` instead";

// Transient: parse_pattern is only consumed by tests until Task 8 wires it
// into parse_match_expr. Removed in Task 8.
#[allow(dead_code)]
pub(crate) fn parse_pattern(p: &mut Parser) -> Result<Pattern, CompileError> {
    let start = p.current_span();
    let tok = p.peek().clone();
    match &tok.kind {
        TokenKind::Ident(name) if name == "_" => {
            p.advance();
            Ok(Pattern {
                kind: PatternKind::Wildcard,
                span: tok.span,
            })
        }
        TokenKind::Ident(name) => {
            let n = name.clone();
            p.advance();
            if p.eat(&TokenKind::LParen) {
                p.consume_newlines();
                let mut payload = Vec::new();
                if !p.at(&TokenKind::RParen) {
                    payload.push(parse_pattern(p)?);
                    p.consume_newlines();
                    while p.eat(&TokenKind::Comma) {
                        p.consume_newlines();
                        if p.at(&TokenKind::RParen) {
                            break;
                        }
                        payload.push(parse_pattern(p)?);
                        p.consume_newlines();
                    }
                }
                let end = p.current_span();
                p.expect(&TokenKind::RParen, "')'")?;
                Ok(Pattern {
                    kind: PatternKind::Variant(n, payload),
                    span: Span::merge(start, end),
                })
            } else {
                Ok(Pattern {
                    kind: PatternKind::Ident(n),
                    span: tok.span,
                })
            }
        }
        TokenKind::Int(n) => {
            let v = *n;
            p.advance();
            Ok(Pattern {
                kind: PatternKind::IntLit(v),
                span: tok.span,
            })
        }
        TokenKind::Minus => {
            p.advance();
            let next = p.peek().clone();
            match next.kind {
                TokenKind::Int(n) => {
                    p.advance();
                    Ok(Pattern {
                        kind: PatternKind::IntLit(-n),
                        span: Span::merge(tok.span, next.span),
                    })
                }
                TokenKind::Float(_) => Err(CompileError::parse(
                    Span::merge(tok.span, next.span),
                    FLOAT_PATTERN_REJECTED,
                )),
                _ => Err(CompileError::parse(
                    next.span,
                    format!(
                        "expected integer literal after '-' in pattern, found {:?}",
                        next.kind
                    ),
                )),
            }
        }
        TokenKind::Float(_) => Err(CompileError::parse(tok.span, FLOAT_PATTERN_REJECTED)),
        TokenKind::True => {
            p.advance();
            Ok(Pattern {
                kind: PatternKind::BoolLit(true),
                span: tok.span,
            })
        }
        TokenKind::False => {
            p.advance();
            Ok(Pattern {
                kind: PatternKind::BoolLit(false),
                span: tok.span,
            })
        }
        TokenKind::Str(s) => {
            let s = s.clone();
            p.advance();
            Ok(Pattern {
                kind: PatternKind::StrLit(s),
                span: tok.span,
            })
        }
        _ => Err(CompileError::parse(
            tok.span,
            format!("expected pattern, found {:?}", tok.kind),
        )),
    }
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
        assert_eq!(parse(r#""hello""#).kind, ExprKind::StrLit("hello".into()));
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
    fn multi_line_vector_literal() {
        // Newlines inside [ ... ] are ignored.
        let src = "[\n  1.0,\n  2.0,\n  3.0\n]";
        match parse(src).kind {
            ExprKind::VecLit(v) => assert_eq!(v.len(), 3),
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    #[test]
    fn multi_line_matrix_literal() {
        let src = "[\n  [1.0, 0.0, 0.0],\n  [0.0, 1.0, 0.0],\n  [0.0, 0.0, 1.0]\n]";
        match parse(src).kind {
            ExprKind::MatLit(m) => {
                assert_eq!(m.len(), 3);
                assert_eq!(m[0].len(), 3);
            }
            other => panic!("expected MatLit, got {other:?}"),
        }
    }

    #[test]
    fn trailing_comma_vector_literal() {
        match parse("[1.0, 2.0, 3.0,]").kind {
            ExprKind::VecLit(v) => assert_eq!(v.len(), 3),
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    #[test]
    fn trailing_comma_matrix_rows() {
        match parse("[[1, 2], [3, 4],]").kind {
            ExprKind::MatLit(m) => assert_eq!(m.len(), 2),
            other => panic!("expected MatLit, got {other:?}"),
        }
    }

    #[test]
    fn trailing_comma_inside_matrix_row() {
        match parse("[[1, 2,], [3, 4,]]").kind {
            ExprKind::MatLit(m) => {
                assert_eq!(m.len(), 2);
                assert_eq!(m[0].len(), 2);
            }
            other => panic!("expected MatLit, got {other:?}"),
        }
    }

    #[test]
    fn multi_line_with_trailing_comma_combined() {
        let src = "[\n  1.0,\n  2.0,\n  3.0,\n]";
        match parse(src).kind {
            ExprKind::VecLit(v) => assert_eq!(v.len(), 3),
            other => panic!("expected VecLit, got {other:?}"),
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
    fn neg_binds_below_pow() {
        // Per Design Doc §6.6, unary `-` (precedence 7) is below `^` (8).
        // `-x^2` must parse as Neg(Pow(x, 2)) — Python/Fortran convention.
        // Critical for physics DSL: e^(-x^2) (Gaussian) must mean exp(-(x^2)).
        let e = parse("-x^2");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Neg, inner) => {
                assert!(matches!(inner.kind, ExprKind::BinOp(BinOp::Pow, _, _)));
            }
            _ => panic!("expected Neg(Pow), got {:?}", e.kind),
        }
    }

    #[test]
    fn neg_with_pow_chain() {
        // `-2^3^4` must parse as Neg(Pow(2, Pow(3, 4))) since ^ is right-assoc
        // and unary - sits below ^ in precedence.
        let e = parse("-2^3^4");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Neg, inner) => match inner.kind {
                ExprKind::BinOp(BinOp::Pow, lhs, rhs) => {
                    assert_eq!(lhs.kind, ExprKind::IntLit(2));
                    assert!(matches!(rhs.kind, ExprKind::BinOp(BinOp::Pow, _, _)));
                }
                _ => panic!("expected outer Pow inside Neg"),
            },
            _ => panic!("expected Neg(Pow), got {:?}", e.kind),
        }
    }

    #[test]
    fn neg_binds_above_mul() {
        // `-x * y` must parse as Mul(Neg(x), y), not Neg(Mul(x, y)).
        // Unary - (7) is above * (6).
        let e = parse("-x * y");
        match e.kind {
            ExprKind::BinOp(BinOp::Mul, lhs, _) => {
                assert!(matches!(lhs.kind, ExprKind::UnaryOp(UnaryOp::Neg, _)));
            }
            _ => panic!("expected Mul at root, got {:?}", e.kind),
        }
    }

    #[test]
    fn neg_call_remains_postfix() {
        // `-f(x)` parses as Neg(Call(f, x)) — call/index/field bind tighter than unary -.
        let e = parse("-f(x)");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Neg, inner) => {
                assert!(matches!(inner.kind, ExprKind::Call(_, _)));
            }
            _ => panic!("expected Neg(Call), got {:?}", e.kind),
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
    fn not_binds_below_comparison() {
        // Per Design Doc §6.6, `not` has precedence 3 (below comparison 4).
        // `not 1 == 2` must parse as Not(Eq(1, 2)).
        let e = parse("not 1 == 2");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Not, inner) => {
                assert!(matches!(inner.kind, ExprKind::BinOp(BinOp::Eq, _, _)));
            }
            _ => panic!("expected Not(Eq), got {:?}", e.kind),
        }
    }

    #[test]
    fn not_binds_below_arithmetic() {
        // `not 1 + 2` must parse as Not(Add(1, 2)).
        let e = parse("not 1 + 2");
        match e.kind {
            ExprKind::UnaryOp(UnaryOp::Not, inner) => {
                assert!(matches!(inner.kind, ExprKind::BinOp(BinOp::Add, _, _)));
            }
            _ => panic!("expected Not(Add), got {:?}", e.kind),
        }
    }

    #[test]
    fn not_with_logical_and() {
        // `a or not b and c` should parse as Or(a, And(Not(b), c))
        // because not (3) > and (2) > or (1).
        let e = parse("a or not b and c");
        match e.kind {
            ExprKind::BinOp(BinOp::Or, _, rhs) => match rhs.kind {
                ExprKind::BinOp(BinOp::And, lhs2, _) => {
                    assert!(matches!(lhs2.kind, ExprKind::UnaryOp(UnaryOp::Not, _)));
                }
                _ => panic!("expected And on rhs of Or"),
            },
            _ => panic!("expected Or at root, got {:?}", e.kind),
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
    fn function_call_multi_line_args() {
        // Newlines inside call arguments `(...)` should be ignored.
        let e = parse("f(\n  1,\n  2,\n  3\n)");
        match e.kind {
            ExprKind::Call(_, args) => assert_eq!(args.len(), 3),
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn function_call_trailing_comma() {
        let e = parse("f(1, 2,)");
        match e.kind {
            ExprKind::Call(_, args) => assert_eq!(args.len(), 2),
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn function_call_multi_line_with_trailing_comma() {
        let e = parse("f(\n  1,\n  2,\n)");
        match e.kind {
            ExprKind::Call(_, args) => assert_eq!(args.len(), 2),
            other => panic!("expected Call, got {other:?}"),
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

    #[test]
    fn if_then_else_end() {
        let source = "if x > 0 then\n  return 1\nelse\n  return -1\nend";
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        let e = parse_expr(&mut p).unwrap();
        match e.kind {
            ExprKind::If(ie) => {
                assert!(ie.else_block.is_some());
                assert_eq!(ie.elseifs.len(), 0);
            }
            _ => panic!("expected If"),
        }
    }

    #[test]
    fn if_with_elseif() {
        let source =
            "if x > 0 then\n  return 1\nelseif x == 0 then\n  return 0\nelse\n  return -1\nend";
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        let e = parse_expr(&mut p).unwrap();
        if let ExprKind::If(ie) = e.kind {
            assert_eq!(ie.elseifs.len(), 1);
        } else {
            panic!("expected If");
        }
    }

    fn parse_pat(source: &str) -> crate::ast::Pattern {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        super::parse_pattern(&mut p).unwrap()
    }

    #[test]
    fn pattern_wildcard() {
        let p = parse_pat("_");
        assert!(matches!(p.kind, crate::ast::PatternKind::Wildcard));
    }

    #[test]
    fn pattern_ident_binding() {
        let p = parse_pat("x");
        match p.kind {
            crate::ast::PatternKind::Ident(name) => assert_eq!(name, "x"),
            other => panic!("expected Ident, got {other:?}"),
        }
    }

    #[test]
    fn pattern_no_payload_variant_parses_as_ident() {
        // No-payload variant lexes as Ident; semantic phase resolves whether it
        // is a variant or a free binding.
        let p = parse_pat("None");
        match p.kind {
            crate::ast::PatternKind::Ident(name) => assert_eq!(name, "None"),
            other => panic!("expected Ident, got {other:?}"),
        }
    }

    #[test]
    fn pattern_variant_one_payload() {
        let p = parse_pat("Some(x)");
        match p.kind {
            crate::ast::PatternKind::Variant(name, payload) => {
                assert_eq!(name, "Some");
                assert_eq!(payload.len(), 1);
                assert!(matches!(payload[0].kind, crate::ast::PatternKind::Ident(_)));
            }
            other => panic!("expected Variant, got {other:?}"),
        }
    }

    #[test]
    fn pattern_variant_multi_payload() {
        let p = parse_pat("Total(a, b)");
        match p.kind {
            crate::ast::PatternKind::Variant(name, payload) => {
                assert_eq!(name, "Total");
                assert_eq!(payload.len(), 2);
            }
            other => panic!("expected Variant, got {other:?}"),
        }
    }

    #[test]
    fn pattern_nested_variant() {
        let p = parse_pat("Ok(Some(x))");
        match p.kind {
            crate::ast::PatternKind::Variant(name, payload) => {
                assert_eq!(name, "Ok");
                assert_eq!(payload.len(), 1);
                assert!(matches!(
                    payload[0].kind,
                    crate::ast::PatternKind::Variant(_, _)
                ));
            }
            other => panic!("expected Variant, got {other:?}"),
        }
    }

    #[test]
    fn pattern_variant_multi_line_payload() {
        let p = parse_pat("Total(\n  a,\n  b,\n)");
        match p.kind {
            crate::ast::PatternKind::Variant(_, payload) => assert_eq!(payload.len(), 2),
            other => panic!("expected Variant, got {other:?}"),
        }
    }

    #[test]
    fn pattern_int_literal() {
        let p = parse_pat("42");
        assert_eq!(p.kind, crate::ast::PatternKind::IntLit(42));
    }

    #[test]
    fn pattern_int_literal_negative() {
        let p = parse_pat("-1");
        assert_eq!(p.kind, crate::ast::PatternKind::IntLit(-1));
    }

    #[test]
    fn pattern_bool_literal_true() {
        let p = parse_pat("true");
        assert_eq!(p.kind, crate::ast::PatternKind::BoolLit(true));
    }

    #[test]
    fn pattern_bool_literal_false() {
        let p = parse_pat("false");
        assert_eq!(p.kind, crate::ast::PatternKind::BoolLit(false));
    }

    #[test]
    fn pattern_string_literal() {
        let p = parse_pat(r#""hello""#);
        assert_eq!(p.kind, crate::ast::PatternKind::StrLit("hello".into()));
    }

    #[test]
    fn pattern_variant_with_int_literal_payload() {
        let p = parse_pat("Some(0)");
        match p.kind {
            crate::ast::PatternKind::Variant(name, payload) => {
                assert_eq!(name, "Some");
                assert_eq!(payload[0].kind, crate::ast::PatternKind::IntLit(0));
            }
            other => panic!("expected Variant, got {other:?}"),
        }
    }

    #[test]
    fn pattern_float_literal_rejected() {
        let toks = tokenize("3.14").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_pattern(&mut p).unwrap_err();
        assert!(err.message.contains("floating-point"));
    }

    #[test]
    fn pattern_negative_float_rejected() {
        let toks = tokenize("-3.14").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_pattern(&mut p).unwrap_err();
        assert!(err.message.contains("floating-point"));
    }

    #[test]
    fn pattern_minus_followed_by_non_int_rejected() {
        let toks = tokenize("-x").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_pattern(&mut p).unwrap_err();
        assert!(err.message.contains("expected integer literal after '-'"));
    }
}
