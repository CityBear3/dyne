//! Statement and top-level item parser.

use crate::ast::{Block, ForStmt, LetStmt, Program, Stmt, StmtKind, WhileStmt};
use crate::error::CompileError;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::parser::expr::parse_expr;
use crate::parser::types::parse_type;
use crate::source::Span;

pub(crate) fn parse_program(p: &mut Parser) -> Result<Program, CompileError> {
    p.consume_newlines();
    let start = p.current_span();
    let mut items = Vec::new();
    while !matches!(p.peek_kind(), TokenKind::Eof) {
        // Task 23 will wire top-level items. For now, allow only a bare
        // sequence of statements as a smoke-test path.
        let stmt = parse_stmt(p)?;
        items.push(crate::ast::Item::Let(match stmt.kind {
            StmtKind::Let(l) => l,
            _ => {
                return Err(CompileError::parse(
                    stmt.span,
                    "only `let` is supported at top level until Task 23",
                ));
            }
        }));
        p.consume_newlines();
    }
    let end = p.current_span();
    Ok(Program {
        items,
        span: Span::merge(start, end),
    })
}

pub(crate) fn parse_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    match p.peek_kind() {
        TokenKind::Let => parse_let_stmt(p),
        TokenKind::Return => parse_return_stmt(p),
        TokenKind::While => parse_while_stmt(p),
        TokenKind::For => parse_for_stmt(p),
        TokenKind::Ident(_) if matches!(p.peek_ahead(1), TokenKind::Eq) => {
            parse_assign_stmt(p)
        }
        _ => parse_expr_stmt(p),
    }
}

fn parse_let_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::Let, "'let'")?;
    let name_tok = p.peek().clone();
    let name = match &name_tok.kind {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(CompileError::parse(
                name_tok.span,
                format!("expected identifier after 'let', found {:?}", name_tok.kind),
            ));
        }
    };
    p.advance();
    p.expect(&TokenKind::Colon, "':'")?;
    let ty = parse_type(p)?;
    p.expect(&TokenKind::Eq, "'='")?;
    let init = parse_expr(p)?;
    let span = Span::merge(start, init.span);
    Ok(Stmt {
        kind: StmtKind::Let(LetStmt { name, ty, init }),
        span,
    })
}

fn parse_assign_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let name_tok = p.advance().clone();
    let name = match name_tok.kind {
        TokenKind::Ident(n) => n,
        _ => unreachable!(),
    };
    p.expect(&TokenKind::Eq, "'='")?;
    let expr = parse_expr(p)?;
    let span = Span::merge(name_tok.span, expr.span);
    Ok(Stmt {
        kind: StmtKind::Assign(name, expr),
        span,
    })
}

fn parse_return_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::Return, "'return'")?;
    if matches!(
        p.peek_kind(),
        TokenKind::Newline | TokenKind::Eof | TokenKind::End
    ) {
        return Ok(Stmt {
            kind: StmtKind::Return(None),
            span: start,
        });
    }
    let expr = parse_expr(p)?;
    let span = Span::merge(start, expr.span);
    Ok(Stmt {
        kind: StmtKind::Return(Some(expr)),
        span,
    })
}

fn parse_expr_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let expr = parse_expr(p)?;
    let span = expr.span;
    Ok(Stmt {
        kind: StmtKind::Expr(expr),
        span,
    })
}

fn parse_while_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::While, "'while'")?;
    let cond = parse_expr(p)?;
    p.expect(&TokenKind::Do, "'do'")?;
    let body = parse_block_until(p, &[TokenKindKind::End])?;
    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(Stmt {
        kind: StmtKind::While(WhileStmt { cond, body }),
        span: Span::merge(start, end),
    })
}

fn parse_for_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::For, "'for'")?;
    let name_tok = p.peek().clone();
    let first = match &name_tok.kind {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(CompileError::parse(
                name_tok.span,
                "expected identifier after 'for'",
            ));
        }
    };
    p.advance();

    // Form: `for i = a, b do ... end`
    if p.eat(&TokenKind::Eq) {
        let from = parse_expr(p)?;
        p.expect(&TokenKind::Comma, "','")?;
        let to = parse_expr(p)?;
        p.expect(&TokenKind::Do, "'do'")?;
        let body = parse_block_until(p, &[TokenKindKind::End])?;
        let end = p.current_span();
        p.expect(&TokenKind::End, "'end'")?;
        return Ok(Stmt {
            kind: StmtKind::For(ForStmt::Range {
                var: first,
                start: from,
                end: to,
                body,
            }),
            span: Span::merge(start, end),
        });
    }

    // Form: `for k, v in e do ... end`
    if p.eat(&TokenKind::Comma) {
        let second_tok = p.peek().clone();
        let second = match &second_tok.kind {
            TokenKind::Ident(n) => n.clone(),
            _ => {
                return Err(CompileError::parse(
                    second_tok.span,
                    "expected identifier after ','",
                ));
            }
        };
        p.advance();
        p.expect(&TokenKind::In, "'in'")?;
        let iter = parse_expr(p)?;
        p.expect(&TokenKind::Do, "'do'")?;
        let body = parse_block_until(p, &[TokenKindKind::End])?;
        let end = p.current_span();
        p.expect(&TokenKind::End, "'end'")?;
        return Ok(Stmt {
            kind: StmtKind::For(ForStmt::IterKV {
                key: first,
                value: second,
                iter,
                body,
            }),
            span: Span::merge(start, end),
        });
    }

    // Form: `for x in e do ... end`
    p.expect(&TokenKind::In, "'in'")?;
    let iter = parse_expr(p)?;
    p.expect(&TokenKind::Do, "'do'")?;
    let body = parse_block_until(p, &[TokenKindKind::End])?;
    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(Stmt {
        kind: StmtKind::For(ForStmt::Iter {
            var: first,
            iter,
            body,
        }),
        span: Span::merge(start, end),
    })
}

/// Parse a block that ends at any of: End, Else, Elseif.
pub(crate) fn parse_block_until(
    p: &mut Parser,
    terminators: &[TokenKindKind],
) -> Result<Block, CompileError> {
    let start = p.current_span();
    p.consume_newlines();
    let mut stmts = Vec::new();
    while !is_at_terminator(p, terminators) {
        if matches!(p.peek_kind(), TokenKind::Eof) {
            return Err(CompileError::parse(
                p.current_span(),
                "unexpected end of input inside block",
            ));
        }
        let stmt = parse_stmt(p)?;
        stmts.push(stmt);
        p.consume_newlines();
    }
    let end = p.current_span();
    Ok(Block {
        stmts,
        span: Span::merge(start, end),
    })
}

/// Discriminator enum for block terminators, to avoid needing full TokenKind equality.
#[derive(Clone, Copy)]
pub(crate) enum TokenKindKind {
    End,
    Else,
    Elseif,
}

fn is_at_terminator(p: &Parser, terminators: &[TokenKindKind]) -> bool {
    for t in terminators {
        let matched = match t {
            TokenKindKind::End => matches!(p.peek_kind(), TokenKind::End),
            TokenKindKind::Else => matches!(p.peek_kind(), TokenKind::Else),
            TokenKindKind::Elseif => matches!(p.peek_kind(), TokenKind::Elseif),
        };
        if matched {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprKind;
    use crate::lexer::tokenize;

    fn parse_one(source: &str) -> Stmt {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        parse_stmt(&mut p).unwrap()
    }

    #[test]
    fn let_stmt_scalar() {
        let s = parse_one("let x: Scalar = 1.0");
        match s.kind {
            StmtKind::Let(l) => {
                assert_eq!(l.name, "x");
                assert!(matches!(l.init.kind, ExprKind::FloatLit(_)));
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn let_stmt_vec() {
        let s = parse_one("let v: Vec<3> = [1.0, 2.0, 3.0]");
        if let StmtKind::Let(l) = s.kind {
            assert!(matches!(l.init.kind, ExprKind::VecLit(_)));
        } else {
            panic!("expected Let");
        }
    }

    #[test]
    fn let_with_unit() {
        let s = parse_one("let m: Scalar<kg> = 1.5");
        if let StmtKind::Let(l) = s.kind {
            assert_eq!(l.name, "m");
        } else {
            panic!("expected Let");
        }
    }

    #[test]
    fn assign_stmt() {
        let s = parse_one("x = 2.0");
        match s.kind {
            StmtKind::Assign(name, _) => assert_eq!(name, "x"),
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn return_with_value() {
        let s = parse_one("return 1 + 2");
        match s.kind {
            StmtKind::Return(Some(_)) => {}
            _ => panic!("expected Return(Some)"),
        }
    }

    #[test]
    fn return_without_value() {
        let s = parse_one("return");
        match s.kind {
            StmtKind::Return(None) => {}
            _ => panic!("expected Return(None)"),
        }
    }

    #[test]
    fn while_loop() {
        let s = parse_one("while x > 0 do\n  x = x - 1\nend");
        assert!(matches!(s.kind, StmtKind::While(_)));
    }

    #[test]
    fn for_range() {
        let s = parse_one("for i = 0, 3 do\n  x = i\nend");
        match s.kind {
            StmtKind::For(crate::ast::ForStmt::Range { var, .. }) => assert_eq!(var, "i"),
            _ => panic!("expected For::Range"),
        }
    }

    #[test]
    fn for_iter() {
        let s = parse_one("for x in arr do\n  y = x\nend");
        match s.kind {
            StmtKind::For(crate::ast::ForStmt::Iter { var, .. }) => assert_eq!(var, "x"),
            _ => panic!("expected For::Iter"),
        }
    }

    #[test]
    fn for_iter_kv() {
        let s = parse_one("for k, v in params do\n  x = v\nend");
        match s.kind {
            StmtKind::For(crate::ast::ForStmt::IterKV { key, value, .. }) => {
                assert_eq!(key, "k");
                assert_eq!(value, "v");
            }
            _ => panic!("expected For::IterKV"),
        }
    }
}
