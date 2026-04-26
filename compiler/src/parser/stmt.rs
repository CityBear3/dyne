//! Statement and top-level item parser.

use crate::ast::{
    Block, ForStmt, FunctionDef, Item, LetStmt, Param, Program, Stmt, StmtKind, WhileStmt,
};
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
        let item = parse_item(p)?;
        items.push(item);
        require_stmt_terminator(p, &[])?;
        p.consume_newlines();
    }
    let end = p.current_span();
    Ok(Program {
        items,
        span: Span::merge(start, end),
    })
}

fn parse_item(p: &mut Parser) -> Result<Item, CompileError> {
    match p.peek_kind() {
        TokenKind::Function => Ok(Item::Function(parse_function_def(p)?)),
        TokenKind::Let => {
            let stmt = parse_let_stmt(p)?;
            if let StmtKind::Let(l) = stmt.kind {
                Ok(Item::Let(l))
            } else {
                unreachable!()
            }
        }
        _ => Err(CompileError::parse(
            p.current_span(),
            format!(
                "expected top-level item (function or let), found {:?}",
                p.peek_kind()
            ),
        )),
    }
}

pub(crate) fn parse_stmt(p: &mut Parser) -> Result<Stmt, CompileError> {
    match p.peek_kind() {
        TokenKind::Let => parse_let_stmt(p),
        TokenKind::Return => parse_return_stmt(p),
        TokenKind::While => parse_while_stmt(p),
        TokenKind::For => parse_for_stmt(p),
        TokenKind::Ident(_) if matches!(p.peek_ahead(1), TokenKind::Eq) => parse_assign_stmt(p),
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

fn parse_function_def(p: &mut Parser) -> Result<FunctionDef, CompileError> {
    let start = p.current_span();
    p.expect(&TokenKind::Function, "'function'")?;
    let name_tok = p.peek().clone();
    let name = match &name_tok.kind {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(CompileError::parse(name_tok.span, "expected function name"));
        }
    };
    p.advance();
    p.expect(&TokenKind::LParen, "'('")?;
    p.consume_newlines();
    let mut params = Vec::new();
    if !p.at(&TokenKind::RParen) {
        params.push(parse_param(p)?);
        p.consume_newlines();
        while p.eat(&TokenKind::Comma) {
            p.consume_newlines();
            if p.at(&TokenKind::RParen) {
                break; // trailing comma
            }
            params.push(parse_param(p)?);
            p.consume_newlines();
        }
    }
    p.expect(&TokenKind::RParen, "')'")?;
    p.expect(&TokenKind::Colon, "':'")?;
    let return_ty = parse_type(p)?;
    let body = parse_block_until(p, &[TokenKindKind::End])?;
    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(FunctionDef {
        name,
        params,
        return_ty,
        body,
        span: Span::merge(start, end),
    })
}

fn parse_param(p: &mut Parser) -> Result<Param, CompileError> {
    let name_tok = p.peek().clone();
    let name = match &name_tok.kind {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(CompileError::parse(
                name_tok.span,
                "expected parameter name",
            ));
        }
    };
    p.advance();
    p.expect(&TokenKind::Colon, "':'")?;
    let ty = parse_type(p)?;
    let span = Span::merge(name_tok.span, ty.span);
    Ok(Param { name, ty, span })
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
        require_stmt_terminator(p, terminators)?;
        p.consume_newlines();
    }
    let end = p.current_span();
    Ok(Block {
        stmts,
        span: Span::merge(start, end),
    })
}

/// Require a statement boundary: Newline / Eof / a block terminator.
/// Per Design Doc §6.6, statements must end with one of these.
fn require_stmt_terminator(p: &Parser, terminators: &[TokenKindKind]) -> Result<(), CompileError> {
    if matches!(p.peek_kind(), TokenKind::Newline | TokenKind::Eof)
        || is_at_terminator(p, terminators)
    {
        return Ok(());
    }
    let tok = p.peek();
    Err(CompileError::parse(
        tok.span,
        format!("expected newline after statement, found {:?}", tok.kind),
    ))
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

    fn parse_prog(source: &str) -> Program {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        parse_program(&mut p).unwrap()
    }

    #[test]
    fn program_with_function() {
        let p = parse_prog("function add(a: Scalar, b: Scalar): Scalar\n  return a + b\nend");
        assert_eq!(p.items.len(), 1);
        match &p.items[0] {
            crate::ast::Item::Function(f) => {
                assert_eq!(f.name, "add");
                assert_eq!(f.params.len(), 2);
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn function_signature_multi_line_params() {
        // Newlines inside the parameter list `(...)` should be ignored,
        // mirroring Vec/Mat literal multi-line behaviour.
        let src = "function add(\n  a: Scalar,\n  b: Scalar\n): Scalar\n  return a + b\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Function(f) = &p.items[0] {
            assert_eq!(f.params.len(), 2);
        } else {
            panic!("expected Function");
        }
    }

    #[test]
    fn function_signature_trailing_comma() {
        let src = "function add(a: Scalar, b: Scalar,): Scalar\n  return a + b\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Function(f) = &p.items[0] {
            assert_eq!(f.params.len(), 2);
        } else {
            panic!("expected Function");
        }
    }

    #[test]
    fn function_signature_multi_line_with_trailing_comma() {
        let src = "function add(\n  a: Scalar,\n  b: Scalar,\n): Scalar\n  return a + b\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Function(f) = &p.items[0] {
            assert_eq!(f.params.len(), 2);
        } else {
            panic!("expected Function");
        }
    }

    #[test]
    fn program_with_let_and_function() {
        let src = "let g: Scalar = 9.8\nfunction f(x: Scalar): Scalar\n  return x * g\nend";
        let p = parse_prog(src);
        assert_eq!(p.items.len(), 2);
        assert!(matches!(p.items[0], crate::ast::Item::Let(_)));
        assert!(matches!(p.items[1], crate::ast::Item::Function(_)));
    }

    #[test]
    fn empty_program() {
        let p = parse_prog("");
        assert_eq!(p.items.len(), 0);
    }

    fn parse_prog_err(source: &str) -> CompileError {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        parse_program(&mut p).unwrap_err()
    }

    #[test]
    fn top_level_items_require_newline_separator() {
        // Per Design Doc §6.6: a Newline / Eof / terminator must follow each statement.
        // Two items without a separating Newline must fail.
        let err = parse_prog_err("let x: Int = 1 let y: Int = 2");
        assert!(err.message.contains("newline"));
    }

    #[test]
    fn block_stmts_require_newline_separator() {
        // Same rule inside a block.
        let src = "function f(): Int\n  let a: Int = 1 let b: Int = 2\nend";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("newline"));
    }

    #[test]
    fn one_line_if_as_function_body_still_works() {
        // 1-line if/while/for must still parse: block-open Newline remains optional.
        let src = "function abs1(x: Int): Int\n  if x < 0 then return -1 end\nend";
        let p = parse_prog(src);
        assert_eq!(p.items.len(), 1);
    }

    #[test]
    fn newline_after_each_top_level_item_works() {
        let p = parse_prog("let x: Int = 1\nlet y: Int = 2\n");
        assert_eq!(p.items.len(), 2);
    }
}
