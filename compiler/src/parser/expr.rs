//! Expression parser.

use crate::ast::{BinOp, Block, Expr, ExprKind, IfExpr, MatchArm, Pattern, PatternKind, UnaryOp};
use crate::error::CompileError;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::parser::stmt::{
    EmptyHandling, TokenKindKind, parse_block_until, parse_comma_list, parse_stmt,
};
use crate::source::Span;

pub(crate) fn parse_expr(p: &mut Parser) -> Result<Expr, CompileError> {
    parse_bp(p, 0)
}

fn parse_primary(p: &mut Parser) -> Result<Expr, CompileError> {
    match p.peek_kind() {
        TokenKind::Int(n) => {
            let v = *n;
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::IntLit(v),
                span,
            })
        }
        TokenKind::Float(n) => {
            let v = *n;
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::FloatLit(v),
                span,
            })
        }
        TokenKind::Str(s) => {
            let s = s.clone();
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::StrLit(s),
                span,
            })
        }
        TokenKind::True => {
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::BoolLit(true),
                span,
            })
        }
        TokenKind::False => {
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::BoolLit(false),
                span,
            })
        }
        TokenKind::Ident(name) => {
            let name = name.clone();
            let span = p.advance().span;
            Ok(Expr {
                kind: ExprKind::Ident(name),
                span,
            })
        }
        TokenKind::LParen => {
            let start = p.advance().span;
            let inner = parse_expr(p)?;
            let end = p.peek().span;
            p.expect(&TokenKind::RParen, "')'")?;
            Ok(Expr {
                kind: inner.kind,
                span: Span::merge(start, end),
            })
        }
        TokenKind::LBracket => parse_vec_or_mat_lit(p),
        TokenKind::If => parse_if_expr(p),
        TokenKind::Match => parse_match_expr(p),
        other => {
            let span = p.current_span();
            Err(CompileError::parse(
                span,
                format!("expected expression, found {other:?}"),
            ))
        }
    }
}

fn parse_vec_or_mat_lit(p: &mut Parser) -> Result<Expr, CompileError> {
    let start = p.peek().span;
    p.advance(); // consume '['
    p.consume_newlines();
    // Matrix if first element is '['
    if p.at(&TokenKind::LBracket) {
        let rows = parse_comma_list(p, &TokenKind::RBracket, EmptyHandling::Allow, parse_row)?;
        let end = p.peek().span;
        p.expect(&TokenKind::RBracket, "']'")?;
        return Ok(Expr {
            kind: ExprKind::MatLit(rows),
            span: Span::merge(start, end),
        });
    }
    // Vector literal (possibly empty)
    let elems = parse_comma_list(p, &TokenKind::RBracket, EmptyHandling::Allow, parse_expr)?;
    let end = p.peek().span;
    p.expect(&TokenKind::RBracket, "']'")?;
    Ok(Expr {
        kind: ExprKind::VecLit(elems),
        span: Span::merge(start, end),
    })
}

fn parse_if_expr(p: &mut Parser) -> Result<Expr, CompileError> {
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
                let args =
                    parse_comma_list(p, &TokenKind::RParen, EmptyHandling::Allow, parse_expr)?;
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
                let field = match p.peek_kind() {
                    TokenKind::Ident(n) => n.clone(),
                    other => {
                        return Err(CompileError::parse(
                            p.current_span(),
                            format!("expected field name, found {other:?}"),
                        ));
                    }
                };
                let field_span = p.advance().span;
                let span = Span::merge(expr.span, field_span);
                expr = Expr {
                    kind: ExprKind::FieldAccess(Box::new(expr), field),
                    span,
                };
            }
            TokenKind::LBrace => {
                let name = if let ExprKind::Ident(n) = &expr.kind {
                    n.clone()
                } else {
                    break;
                };
                p.advance();
                let fields = parse_comma_list(
                    p,
                    &TokenKind::RBrace,
                    EmptyHandling::Allow,
                    parse_struct_lit_field,
                )?;
                let end = p.current_span();
                p.expect(&TokenKind::RBrace, "'}'")?;
                let span = Span::merge(expr.span, end);
                expr = Expr {
                    kind: ExprKind::StructLit(name, fields),
                    span,
                };
            }
            _ => break,
        }
    }
    Ok(expr)
}

fn parse_struct_lit_field(p: &mut Parser) -> Result<(String, Expr), CompileError> {
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => return Err(CompileError::parse(p.current_span(), "expected field name")),
    };
    p.advance();
    p.expect(&TokenKind::Colon, "':'")?;
    let value = parse_expr(p)?;
    Ok((name, value))
}

fn parse_row(p: &mut Parser) -> Result<Vec<Expr>, CompileError> {
    p.expect(&TokenKind::LBracket, "'['")?;
    let row = parse_comma_list(p, &TokenKind::RBracket, EmptyHandling::Allow, parse_expr)?;
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

const FLOAT_PATTERN_REJECTED: &str = "floating-point literal patterns are rejected: IEEE 754 equality is unreliable (NaN \u{2260} NaN, rounding error). Only Int / Bool / String literal patterns are supported in `case` arms.";

pub(crate) fn parse_pattern(p: &mut Parser) -> Result<Pattern, CompileError> {
    let start = p.current_span();
    match p.peek_kind() {
        TokenKind::Ident(name) if name == "_" => {
            let span = p.advance().span;
            Ok(Pattern {
                kind: PatternKind::Wildcard,
                span,
            })
        }
        TokenKind::Ident(name) => {
            let n = name.clone();
            let ident_span = p.advance().span;
            if p.eat(&TokenKind::LParen) {
                let payload = parse_comma_list(
                    p,
                    &TokenKind::RParen,
                    EmptyHandling::Reject(
                        "empty payload list `()` is not allowed; use the variant name without parentheses",
                    ),
                    parse_pattern,
                )?;
                let end = p.current_span();
                p.expect(&TokenKind::RParen, "')'")?;
                Ok(Pattern {
                    kind: PatternKind::Variant(n, payload),
                    span: Span::merge(start, end),
                })
            } else {
                Ok(Pattern {
                    kind: PatternKind::Ident(n),
                    span: ident_span,
                })
            }
        }
        TokenKind::Int(n) => {
            let v = *n;
            let span = p.advance().span;
            Ok(Pattern {
                kind: PatternKind::IntLit(v),
                span,
            })
        }
        TokenKind::Minus => {
            p.advance();
            match p.peek_kind() {
                TokenKind::Int(n) => {
                    let v = *n;
                    let int_span = p.advance().span;
                    Ok(Pattern {
                        kind: PatternKind::IntLit(-v),
                        span: Span::merge(start, int_span),
                    })
                }
                TokenKind::Float(_) => {
                    let float_span = p.current_span();
                    Err(CompileError::parse(
                        Span::merge(start, float_span),
                        FLOAT_PATTERN_REJECTED,
                    ))
                }
                other => {
                    let span = p.current_span();
                    Err(CompileError::parse(
                        span,
                        format!("expected integer literal after '-' in pattern, found {other:?}"),
                    ))
                }
            }
        }
        TokenKind::Float(_) => Err(CompileError::parse(start, FLOAT_PATTERN_REJECTED)),
        TokenKind::True => {
            let span = p.advance().span;
            Ok(Pattern {
                kind: PatternKind::BoolLit(true),
                span,
            })
        }
        TokenKind::False => {
            let span = p.advance().span;
            Ok(Pattern {
                kind: PatternKind::BoolLit(false),
                span,
            })
        }
        TokenKind::Str(s) => {
            let s = s.clone();
            let span = p.advance().span;
            Ok(Pattern {
                kind: PatternKind::StrLit(s),
                span,
            })
        }
        other => {
            let span = p.current_span();
            Err(CompileError::parse(
                span,
                format!("expected pattern, found {other:?}"),
            ))
        }
    }
}

fn parse_match_expr(p: &mut Parser) -> Result<Expr, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::Match, "'match'")?;
    let scrutinee = parse_expr(p)?;
    p.consume_newlines();

    let mut arms = Vec::new();
    while !matches!(p.peek_kind(), TokenKind::End) {
        if matches!(p.peek_kind(), TokenKind::Eof) {
            return Err(CompileError::parse(
                p.current_span(),
                "unexpected end of input inside match expression",
            ));
        }
        // Capture span of `case` BEFORE consuming, so the arm span includes
        // the keyword (not just `pattern then body`).
        let case_span = p.current_span();
        p.expect(&TokenKind::Case, "'case'")?;
        let pattern = parse_pattern(p)?;
        p.expect(&TokenKind::Then, "'then'")?;
        let body = parse_match_arm_body(p)?;
        let arm_span = Span::merge(case_span, body.span);
        arms.push(MatchArm {
            pattern,
            body,
            span: arm_span,
        });
    }

    if arms.is_empty() {
        return Err(CompileError::parse(
            p.current_span(),
            "match expression requires at least one `case` arm",
        ));
    }

    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(Expr {
        kind: ExprKind::Match(Box::new(scrutinee), arms),
        span: Span::merge(start, end),
    })
}

fn parse_match_arm_body(p: &mut Parser) -> Result<Block, CompileError> {
    let start = p.current_span();
    p.consume_newlines();
    let mut stmts = Vec::new();
    let mut end_span = start;
    while !matches!(p.peek_kind(), TokenKind::End | TokenKind::Case) {
        if matches!(p.peek_kind(), TokenKind::Eof) {
            return Err(CompileError::parse(
                p.current_span(),
                "unexpected end of input inside match arm body",
            ));
        }
        let stmt = parse_stmt(p)?;
        end_span = stmt.span;
        stmts.push(stmt);
        if !matches!(
            p.peek_kind(),
            TokenKind::Newline | TokenKind::Eof | TokenKind::End | TokenKind::Case
        ) {
            return Err(CompileError::parse(
                p.current_span(),
                format!(
                    "expected newline after match arm statement, found {:?}",
                    p.peek_kind()
                ),
            ));
        }
        p.consume_newlines();
    }
    Ok(Block {
        stmts,
        span: Span::merge(start, end_span),
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

    #[test]
    fn struct_lit_simple() {
        let e = parse("Point { x: 1.0, y: 2.0 }");
        match e.kind {
            ExprKind::StructLit(name, fields) => {
                assert_eq!(name, "Point");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "x");
                assert_eq!(fields[1].0, "y");
            }
            other => panic!("expected StructLit, got {other:?}"),
        }
    }

    #[test]
    fn struct_lit_empty() {
        let e = parse("Marker {}");
        match e.kind {
            ExprKind::StructLit(name, fields) => {
                assert_eq!(name, "Marker");
                assert!(fields.is_empty());
            }
            other => panic!("expected StructLit, got {other:?}"),
        }
    }

    #[test]
    fn struct_lit_multi_line() {
        let e = parse("State {\n  q: [1.0, 0.0, 0.0],\n  p: [0.0, 1.0, 0.0],\n  t: 0.0,\n}");
        match e.kind {
            ExprKind::StructLit(_, fields) => assert_eq!(fields.len(), 3),
            other => panic!("expected StructLit, got {other:?}"),
        }
    }

    #[test]
    fn struct_lit_used_in_let() {
        let toks = tokenize("let s: State = State { q: 1.0, p: 0.0 }").unwrap();
        let mut parser = Parser::new(&toks);
        let prog = crate::parser::stmt::parse_program(&mut parser).unwrap();
        assert_eq!(prog.items.len(), 1);
    }

    #[test]
    fn lbrace_after_non_ident_does_not_form_struct_lit() {
        let toks = tokenize("f() { x: 1 }").unwrap();
        let mut p = Parser::new(&toks);
        let e = super::parse_expr(&mut p).unwrap();
        assert!(matches!(e.kind, ExprKind::Call(_, _)));
        // The `{` must remain unconsumed — postfix loop should have broken.
        assert!(matches!(p.peek_kind(), TokenKind::LBrace));
    }

    #[test]
    fn struct_lit_non_ident_field_rejected() {
        let toks = tokenize("Point { 1: x }").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_expr(&mut p).unwrap_err();
        assert!(err.message.contains("expected field name"));
    }

    #[test]
    fn match_simple() {
        let e = parse("match x\n  case Some(v) then\n    v\n  case None then\n    0\nend");
        match e.kind {
            ExprKind::Match(scrutinee, arms) => {
                assert!(matches!(scrutinee.kind, ExprKind::Ident(_)));
                assert_eq!(arms.len(), 2);
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    #[test]
    fn match_with_wildcard() {
        let e = parse("match x\n  case 0 then\n    1\n  case _ then\n    0\nend");
        if let ExprKind::Match(_, arms) = e.kind {
            assert_eq!(arms.len(), 2);
            assert!(matches!(
                arms[0].pattern.kind,
                crate::ast::PatternKind::IntLit(0)
            ));
            assert!(matches!(
                arms[1].pattern.kind,
                crate::ast::PatternKind::Wildcard
            ));
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_with_int_literal_payload_arm() {
        let e = parse(
            "match x\n  case Some(0) then\n    1\n  case Some(n) then\n    n\n  case None then\n    0\nend",
        );
        if let ExprKind::Match(_, arms) = e.kind {
            assert_eq!(arms.len(), 3);
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_zero_arms_rejected() {
        let toks = tokenize("match x\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(err.message.contains("at least one"));
    }

    #[test]
    fn match_arm_multi_statement_body() {
        let src = "match x\n  case Some(v) then\n    let r: Int = v + 1\n    r\n  case None then\n    0\nend";
        let e = parse(src);
        if let ExprKind::Match(_, arms) = e.kind {
            assert_eq!(arms[0].body.stmts.len(), 2);
            assert_eq!(arms[1].body.stmts.len(), 1);
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn match_used_in_let_init() {
        let src = "let n: Int = match opt\n  case Some(v) then v\n  case None then 0\nend";
        let toks = tokenize(src).unwrap();
        let mut parser = Parser::new(&toks);
        let prog = crate::parser::stmt::parse_program(&mut parser).unwrap();
        assert_eq!(prog.items.len(), 1);
    }

    #[test]
    fn match_missing_case_keyword_rejected() {
        let toks = tokenize("match x\n  Some(v) then\n    v\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(err.message.contains("'case'"));
    }

    #[test]
    fn match_missing_then_keyword_rejected() {
        let toks = tokenize("match x\n  case Some(v)\n    v\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(err.message.contains("'then'"));
    }

    #[test]
    fn match_eof_inside_expression_rejected() {
        // Reaches the outer Eof guard: scrutinee + newlines, then Eof before the first `case`.
        let toks = tokenize("match x\n").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(
            err.message
                .contains("unexpected end of input inside match expression")
        );
    }

    #[test]
    fn match_eof_inside_arm_body_rejected() {
        let toks = tokenize("match x\n  case _ then\n").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(
            err.message
                .contains("unexpected end of input inside match arm body")
        );
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

    #[test]
    fn match_arm_body_span_does_not_include_next_case() {
        let src = "match x\n  case 0 then 1\n  case _ then 0\nend";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let e = parse_expr(&mut p).unwrap();
        let ExprKind::Match(_, arms) = e.kind else {
            panic!("expected Match");
        };
        let body_text = &src[arms[0].body.span.start..arms[0].body.span.end];
        assert!(
            !body_text.contains("case"),
            "arm[0].body.span overshot into next case: {body_text:?}"
        );
    }

    #[test]
    fn pattern_unsupported_token_rejected() {
        let toks = tokenize("+").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_pattern(&mut p).unwrap_err();
        assert!(err.message.contains("expected pattern"));
    }

    #[test]
    fn match_arm_body_two_stmts_on_one_line_rejected() {
        let toks = tokenize("match x\n  case _ then 1 1\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_expr(&mut p).unwrap_err();
        assert!(
            err.message
                .contains("expected newline after match arm statement")
        );
    }

    #[test]
    fn pattern_variant_empty_payload_rejected() {
        let toks = tokenize("Foo()").unwrap();
        let mut p = Parser::new(&toks);
        let err = super::parse_pattern(&mut p).unwrap_err();
        assert!(err.message.contains("empty payload list"));
    }

    #[test]
    fn last_match_arm_body_span_does_not_include_end() {
        let src = "match x\n  case _ then 0\nend";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let e = parse_expr(&mut p).unwrap();
        let ExprKind::Match(_, arms) = e.kind else {
            panic!("expected Match");
        };
        let body_text = &src[arms[0].body.span.start..arms[0].body.span.end];
        assert!(
            !body_text.contains("end"),
            "last arm body span includes 'end': {body_text:?}"
        );
    }
}
