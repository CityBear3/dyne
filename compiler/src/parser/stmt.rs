//! Statement and top-level item parser.

use crate::ast::{
    Block, EnumDef, EnumVariant, ForStmt, FunctionDef, Item, LetStmt, Param, Program, Stmt,
    StmtKind, StructDef, StructField, WhileStmt,
};
use crate::diag::Diagnostic;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::parser::expr::parse_expr;
use crate::parser::types::parse_type;
use crate::source::Span;

pub(crate) fn parse_program(p: &mut Parser) -> Result<Program, Diagnostic> {
    p.consume_newlines();
    let start = p.current_span();
    let mut items = Vec::new();
    while !matches!(p.peek_kind(), TokenKind::Eof) {
        let item = parse_item(p)?;
        if !matches!(p.peek_kind(), TokenKind::Newline | TokenKind::Eof) {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                format!(
                    "expected newline after statement, found {:?}",
                    p.peek_kind()
                ),
            ));
        }
        items.push(item);
        p.consume_newlines();
    }
    let end = p.current_span();
    Ok(Program {
        items,
        span: Span::merge(start, end),
        id: p.fresh_node_id(),
    })
}

fn parse_item(p: &mut Parser) -> Result<Item, Diagnostic> {
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
        TokenKind::Struct => Ok(Item::Struct(parse_struct_def(p)?)),
        TokenKind::Enum => Ok(Item::Enum(parse_enum_def(p)?)),
        _ => Err(Diagnostic::parse_error(
            p.current_span(),
            format!(
                "expected top-level item (function, let, struct, or enum), found {:?}",
                p.peek_kind()
            ),
        )),
    }
}

fn parse_struct_def(p: &mut Parser) -> Result<StructDef, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::Struct, "'struct'")?;
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                "expected struct name",
            ));
        }
    };
    p.advance();
    p.consume_newlines();
    let mut fields = Vec::new();
    while !matches!(p.peek_kind(), TokenKind::End | TokenKind::Eof) {
        let field_start = p.current_span();
        let fname = match p.peek_kind() {
            TokenKind::Ident(n) => n.clone(),
            _ => {
                return Err(Diagnostic::parse_error(
                    p.current_span(),
                    "expected field name",
                ));
            }
        };
        p.advance();
        p.expect(&TokenKind::Colon, "':'")?;
        let ty = crate::parser::types::parse_type(p)?;
        let span = Span::merge(field_start, ty.span);
        fields.push(StructField {
            name: fname,
            ty,
            span,
            id: p.fresh_node_id(),
        });
        p.eat(&TokenKind::Comma);
        if !matches!(
            p.peek_kind(),
            TokenKind::Newline | TokenKind::End | TokenKind::Eof
        ) {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                format!(
                    "expected newline after struct field, found {:?}",
                    p.peek_kind()
                ),
            ));
        }
        p.consume_newlines();
    }
    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(StructDef {
        name,
        fields,
        span: Span::merge(start, end),
        id: p.fresh_node_id(),
    })
}

fn parse_enum_def(p: &mut Parser) -> Result<EnumDef, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::Enum, "'enum'")?;
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                "expected enum name",
            ));
        }
    };
    p.advance();
    let type_params = crate::parser::types::parse_type_param_list(p)?;
    p.consume_newlines();
    let mut variants = Vec::new();
    while !matches!(p.peek_kind(), TokenKind::End | TokenKind::Eof) {
        variants.push(parse_variant_decl(p)?);
        p.eat(&TokenKind::Comma);
        if !matches!(
            p.peek_kind(),
            TokenKind::Newline | TokenKind::End | TokenKind::Eof
        ) {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                format!(
                    "expected newline after enum variant, found {:?}",
                    p.peek_kind()
                ),
            ));
        }
        p.consume_newlines();
    }
    let end = p.current_span();
    p.expect(&TokenKind::End, "'end'")?;
    Ok(EnumDef {
        name,
        type_params,
        variants,
        span: Span::merge(start, end),
        id: p.fresh_node_id(),
    })
}

fn parse_variant_decl(p: &mut Parser) -> Result<EnumVariant, Diagnostic> {
    let start = p.current_span();
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                "expected variant name",
            ));
        }
    };
    let name_span = p.advance().span;
    let mut payload = Vec::new();
    let mut end_span = name_span;
    if p.eat(&TokenKind::LParen) {
        payload = parse_comma_list(
            p,
            &TokenKind::RParen,
            EmptyHandling::Reject(
                "empty payload list `()` is not allowed; omit the parentheses for a no-payload variant",
            ),
            crate::parser::types::parse_type,
        )?;
        // Capture span of `)` BEFORE consuming, so the variant span doesn't
        // overshoot into the following Newline / Comma / `end` / Eof.
        // Mirrors the call-args precedent in parse_postfix.
        end_span = p.current_span();
        p.expect(&TokenKind::RParen, "')'")?;
    }
    Ok(EnumVariant {
        name,
        payload,
        span: Span::merge(start, end_span),
        id: p.fresh_node_id(),
    })
}

pub(crate) fn parse_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
    match p.peek_kind() {
        TokenKind::Let => parse_let_stmt(p),
        TokenKind::Return => parse_return_stmt(p),
        TokenKind::While => parse_while_stmt(p),
        TokenKind::For => parse_for_stmt(p),
        TokenKind::Ident(_) if matches!(p.peek_ahead(1), TokenKind::Eq) => parse_assign_stmt(p),
        _ => parse_expr_stmt(p),
    }
}

fn parse_let_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::Let, "'let'")?;
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        other => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                format!("expected identifier after 'let', found {other:?}"),
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
        id: p.fresh_node_id(),
    })
}

fn parse_assign_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
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
        id: p.fresh_node_id(),
    })
}

fn parse_return_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::Return, "'return'")?;
    if matches!(
        p.peek_kind(),
        TokenKind::Newline | TokenKind::Eof | TokenKind::End
    ) {
        return Ok(Stmt {
            kind: StmtKind::Return(None),
            span: start,
            id: p.fresh_node_id(),
        });
    }
    let expr = parse_expr(p)?;
    let span = Span::merge(start, expr.span);
    Ok(Stmt {
        kind: StmtKind::Return(Some(expr)),
        span,
        id: p.fresh_node_id(),
    })
}

fn parse_expr_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
    let expr = parse_expr(p)?;
    let span = expr.span;
    Ok(Stmt {
        kind: StmtKind::Expr(expr),
        span,
        id: p.fresh_node_id(),
    })
}

fn parse_while_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
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
        id: p.fresh_node_id(),
    })
}

fn parse_for_stmt(p: &mut Parser) -> Result<Stmt, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::For, "'for'")?;
    let first = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
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
            id: p.fresh_node_id(),
        });
    }

    // Form: `for k, v in e do ... end`
    if p.eat(&TokenKind::Comma) {
        let second = match p.peek_kind() {
            TokenKind::Ident(n) => n.clone(),
            _ => {
                return Err(Diagnostic::parse_error(
                    p.current_span(),
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
            id: p.fresh_node_id(),
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
        id: p.fresh_node_id(),
    })
}

fn parse_function_def(p: &mut Parser) -> Result<FunctionDef, Diagnostic> {
    let start = p.current_span();
    p.expect(&TokenKind::Function, "'function'")?;
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                "expected function name",
            ));
        }
    };
    p.advance();
    p.expect(&TokenKind::LParen, "'('")?;
    let params = parse_comma_list(p, &TokenKind::RParen, EmptyHandling::Allow, parse_param)?;
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
        id: p.fresh_node_id(),
    })
}

fn parse_param(p: &mut Parser) -> Result<Param, Diagnostic> {
    let name = match p.peek_kind() {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                "expected parameter name",
            ));
        }
    };
    let name_span = p.advance().span;
    p.expect(&TokenKind::Colon, "':'")?;
    let ty = parse_type(p)?;
    let span = Span::merge(name_span, ty.span);
    Ok(Param {
        name,
        ty,
        span,
        id: p.fresh_node_id(),
    })
}

/// How `parse_comma_list` should treat an empty list (closing token immediately
/// after the opening boundary).
pub(crate) enum EmptyHandling {
    /// Empty list is allowed; return `Vec::new()`.
    Allow,
    /// Empty list is rejected; emit `Diagnostic::parse_error` with this message.
    Reject(&'static str),
    /// Don't pre-check; let `parse_one` produce its own error if it fails.
    /// Use when the original code did not have an explicit empty check.
    RequireOne,
}

/// Parse a comma-separated list of items terminated by `close`, with optional
/// newlines around items and an optional trailing comma. Caller is responsible
/// for consuming the opening delimiter and the closing delimiter.
pub(crate) fn parse_comma_list<T, F>(
    p: &mut Parser,
    close: &TokenKind,
    empty: EmptyHandling,
    mut parse_one: F,
) -> Result<Vec<T>, Diagnostic>
where
    F: FnMut(&mut Parser) -> Result<T, Diagnostic>,
{
    p.consume_newlines();
    if p.at(close) {
        return match empty {
            EmptyHandling::Allow => Ok(Vec::new()),
            EmptyHandling::Reject(msg) => Err(Diagnostic::parse_error(p.current_span(), msg)),
            EmptyHandling::RequireOne => {
                // Call parse_one which will produce its own error
                // (e.g. parse_type at `>` fails with "expected type name, found Gt").
                Ok(vec![parse_one(p)?])
            }
        };
    }
    let mut items = vec![parse_one(p)?];
    p.consume_newlines();
    while p.eat(&TokenKind::Comma) {
        p.consume_newlines();
        if p.at(close) {
            break;
        }
        items.push(parse_one(p)?);
        p.consume_newlines();
    }
    Ok(items)
}

/// Parse a block body: leading newlines, then statements separated by
/// Newline / Eof / a caller-supplied terminator predicate, until the
/// terminator is at the parser's position.
///
/// The returned Block's span ends at the last consumed statement's span,
/// not at the terminator. Callers compute their own outer span (incl.
/// the terminating keyword) at the call site if needed.
pub(crate) fn parse_block_body<F>(
    p: &mut Parser,
    is_terminator: F,
    eof_msg: &'static str,
    after_stmt_label: &'static str,
) -> Result<Block, Diagnostic>
where
    F: Fn(&Parser) -> bool,
{
    let start = p.current_span();
    p.consume_newlines();
    let mut stmts = Vec::new();
    let mut end_span = start;
    while !is_terminator(p) {
        if matches!(p.peek_kind(), TokenKind::Eof) {
            return Err(Diagnostic::parse_error(p.current_span(), eof_msg));
        }
        let stmt = parse_stmt(p)?;
        end_span = stmt.span;
        stmts.push(stmt);
        if !matches!(p.peek_kind(), TokenKind::Newline | TokenKind::Eof) && !is_terminator(p) {
            return Err(Diagnostic::parse_error(
                p.current_span(),
                format!("{}, found {:?}", after_stmt_label, p.peek_kind()),
            ));
        }
        p.consume_newlines();
    }
    Ok(Block {
        stmts,
        span: Span::merge(start, end_span),
        id: p.fresh_node_id(),
    })
}

/// Parse a block that ends at any of the supplied block terminators
/// (End, Else, Elseif). Used by Stage 1 control-flow forms.
pub(crate) fn parse_block_until(
    p: &mut Parser,
    terminators: &[TokenKindKind],
) -> Result<Block, Diagnostic> {
    parse_block_body(
        p,
        |p| is_at_terminator(p, terminators),
        "unexpected end of input inside block",
        "expected newline after statement",
    )
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

    fn parse_prog_err(source: &str) -> Diagnostic {
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

    #[test]
    fn struct_def_simple() {
        let p = parse_prog("struct Point\n  x: Scalar\n  y: Scalar\nend");
        assert_eq!(p.items.len(), 1);
        if let crate::ast::Item::Struct(s) = &p.items[0] {
            assert_eq!(s.name, "Point");
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].name, "x");
            assert_eq!(s.fields[1].name, "y");
        } else {
            panic!("expected Struct item");
        }
    }

    #[test]
    fn struct_def_empty() {
        let p = parse_prog("struct Marker\nend");
        if let crate::ast::Item::Struct(s) = &p.items[0] {
            assert_eq!(s.name, "Marker");
            assert!(s.fields.is_empty());
        } else {
            panic!("expected Struct item");
        }
    }

    #[test]
    fn struct_def_unit_annotated_fields() {
        let src = "struct State\n  q: Vec<3>\n  p: Vec<3>\n  t: Scalar\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Struct(s) = &p.items[0] {
            assert_eq!(s.fields.len(), 3);
        } else {
            panic!("expected Struct item");
        }
    }

    #[test]
    fn struct_def_trailing_comma_per_field() {
        let src = "struct Pair\n  a: Scalar,\n  b: Scalar,\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Struct(s) = &p.items[0] {
            assert_eq!(s.fields.len(), 2);
        } else {
            panic!("expected Struct item");
        }
    }

    #[test]
    fn struct_def_field_without_newline_rejected() {
        let toks = tokenize("struct Bad\n  x: Scalar y: Scalar\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected newline after struct field"));
    }

    #[test]
    fn enum_def_simple_no_payload() {
        let p = parse_prog("enum Color\n  Red\n  Green\n  Blue\nend");
        if let crate::ast::Item::Enum(e) = &p.items[0] {
            assert_eq!(e.name, "Color");
            assert!(e.type_params.is_empty());
            assert_eq!(e.variants.len(), 3);
            assert_eq!(e.variants[0].name, "Red");
            assert!(e.variants[0].payload.is_empty());
        } else {
            panic!("expected Enum item");
        }
    }

    #[test]
    fn enum_def_with_payload() {
        let src = "enum Energy\n  Kinetic(Scalar)\n  Total(Scalar, Scalar)\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Enum(e) = &p.items[0] {
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].payload.len(), 1);
            assert_eq!(e.variants[1].payload.len(), 2);
        } else {
            panic!("expected Enum item");
        }
    }

    #[test]
    fn enum_def_generic_two_params() {
        let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Enum(e) = &p.items[0] {
            assert_eq!(e.name, "Result");
            assert_eq!(e.type_params, vec!["T".to_string(), "E".to_string()]);
            assert_eq!(e.variants.len(), 2);
        } else {
            panic!("expected Enum item");
        }
    }

    #[test]
    fn enum_def_option_one_param() {
        let src = "enum Option<T>\n  Some(T)\n  None\nend";
        let p = parse_prog(src);
        if let crate::ast::Item::Enum(e) = &p.items[0] {
            assert_eq!(e.type_params, vec!["T".to_string()]);
            assert_eq!(e.variants[0].payload.len(), 1);
            assert_eq!(e.variants[1].payload.len(), 0);
        } else {
            panic!("expected Enum item");
        }
    }

    #[test]
    fn enum_def_variant_without_newline_rejected() {
        let toks = tokenize("enum Bad\n  Red Green\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected newline after enum variant"));
    }

    #[test]
    fn enum_def_missing_type_param_name_rejected() {
        let toks = tokenize("enum Bad<1>\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected type parameter name"));
    }

    #[test]
    fn enum_def_missing_variant_name_rejected() {
        let toks = tokenize("enum Bad\n  1\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected variant name"));
    }

    #[test]
    fn enum_def_empty_type_params_rejected() {
        let toks = tokenize("enum Foo<>\n  V\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("empty type parameter list"));
    }

    #[test]
    fn enum_def_empty_payload_rejected() {
        let toks = tokenize("enum E\n  Foo()\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("empty payload list"));
    }

    #[test]
    fn struct_def_missing_name_rejected() {
        let toks = tokenize("struct 1\n  x: Int\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected struct name"));
    }

    #[test]
    fn struct_def_field_name_missing_rejected() {
        let toks = tokenize("struct S\n  1: Int\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected field name"));
    }

    #[test]
    fn enum_def_missing_name_rejected() {
        let toks = tokenize("enum 1\n  V\nend").unwrap();
        let mut p = Parser::new(&toks);
        let err = parse_program(&mut p).unwrap_err();
        assert!(err.message.contains("expected enum name"));
    }

    /// Pin: `<T, U>` type-parameter lists accept newlines around items and
    /// trailing commas, as a side effect of using `parse_comma_list`. Anchors
    /// the Stage 2 §5.1 multi-line / trailing-comma convention against
    /// future stricter implementations of the helper.
    #[test]
    fn enum_def_type_params_accept_newlines() {
        let toks = tokenize("enum Foo<\n  T,\n  U,\n>\n  V\nend").unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        assert_eq!(prog.items.len(), 1);
        let crate::ast::Item::Enum(ref e) = prog.items[0] else {
            panic!("expected Enum item");
        };
        assert_eq!(e.type_params, vec!["T".to_string(), "U".to_string()]);
    }

    /// Pin: function body `Block.span` does not overshoot into the closing
    /// `end` keyword. Anchors the Task-4 fix (parse_block_body captures
    /// end_span = stmt.span instead of p.current_span()).
    #[test]
    fn function_body_span_does_not_include_end() {
        let src = "function f(): Int\n  return 1\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let crate::ast::Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let body_text = &src[func.body.span.start..func.body.span.end];
        assert!(
            !body_text.contains("end"),
            "function body span overshoots into 'end': {body_text:?}"
        );
    }

    /// Pin: `while` body `Block.span` does not overshoot into the closing
    /// `end` keyword. Anchors the Task-4 fix.
    #[test]
    fn while_body_span_does_not_include_end() {
        let src = "function f(): Int\n  while true do\n    return 1\n  end\n  return 0\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let crate::ast::Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        // Find the While statement inside the function body.
        let while_stmt = func
            .body
            .stmts
            .iter()
            .find(|s| matches!(s.kind, crate::ast::StmtKind::While(_)))
            .expect("expected While stmt");
        let crate::ast::StmtKind::While(ref ws) = while_stmt.kind else {
            unreachable!()
        };
        let body_text = &src[ws.body.span.start..ws.body.span.end];
        assert!(
            !body_text.contains("end"),
            "while body span overshoots into 'end': {body_text:?}"
        );
    }

    /// Pin: `if` then-branch `Block.span` does not overshoot into `else` or
    /// `end`. Anchors the Task-4 fix.
    #[test]
    fn if_then_branch_span_does_not_include_else() {
        let src =
            "function f(): Int\n  if true then\n    return 1\n  else\n    return 2\n  end\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let crate::ast::Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        // First stmt in the body should be ExprStmt(If(...)).
        let first_stmt = &func.body.stmts[0];
        let crate::ast::StmtKind::Expr(ref e) = first_stmt.kind else {
            panic!("expected ExprStmt");
        };
        let crate::ast::ExprKind::If(ref ifx) = e.kind else {
            panic!("expected If expression");
        };
        let then_text = &src[ifx.then_block.span.start..ifx.then_block.span.end];
        assert!(
            !then_text.contains("else"),
            "if then-branch span overshoots into 'else': {then_text:?}"
        );
        assert!(
            !then_text.contains("end"),
            "if then-branch span overshoots into 'end': {then_text:?}"
        );
    }

    /// Anchors the Task-4 fix: `IfExpr.else_block.span` ends at the last
    /// consumed statement in the else branch, not at the closing `end`.
    #[test]
    fn if_else_branch_span_does_not_include_end() {
        let src =
            "function f(): Int\n  if true then\n    return 1\n  else\n    return 2\n  end\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let StmtKind::Expr(ref e) = func.body.stmts[0].kind else {
            panic!("expected ExprStmt");
        };
        let ExprKind::If(ref ifx) = e.kind else {
            panic!("expected If expression");
        };
        let else_block = ifx
            .else_block
            .as_ref()
            .expect("expected else block in fixture");
        let body_text = &src[else_block.span.start..else_block.span.end];
        assert!(
            !body_text.contains("end"),
            "if else-branch span overshoots into 'end': {body_text:?}"
        );
    }

    /// Anchors the Task-4 fix: `IfExpr.elseifs[i].1.span` (the elseif block)
    /// ends at the last consumed statement, not at the next `elseif` / `else`
    /// / `end`.
    #[test]
    fn if_elseif_branch_span_does_not_include_next_keyword() {
        let src = "function f(): Int\n  if false then\n    return 0\n  elseif true then\n    return 1\n  else\n    return 2\n  end\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let StmtKind::Expr(ref e) = func.body.stmts[0].kind else {
            panic!("expected ExprStmt");
        };
        let ExprKind::If(ref ifx) = e.kind else {
            panic!("expected If expression");
        };
        let (_cond, elseif_block) = ifx
            .elseifs
            .first()
            .expect("expected at least one elseif in fixture");
        let body_text = &src[elseif_block.span.start..elseif_block.span.end];
        assert!(
            !body_text.contains("else"),
            "if elseif-branch span overshoots into 'else'/'elseif': {body_text:?}"
        );
        assert!(
            !body_text.contains("end"),
            "if elseif-branch span overshoots into 'end': {body_text:?}"
        );
    }

    /// Anchors the Task-4 fix: `ForStmt::Range.body.span` ends at the last
    /// consumed statement, not at the closing `end`.
    #[test]
    fn for_range_body_span_does_not_include_end() {
        let src = "function f(): Int\n  for i = 0, 10 do\n    return i\n  end\n  return 0\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let for_stmt = func
            .body
            .stmts
            .iter()
            .find(|s| matches!(s.kind, StmtKind::For(_)))
            .expect("expected For stmt");
        let StmtKind::For(ref fs) = for_stmt.kind else {
            unreachable!()
        };
        let ForStmt::Range { ref body, .. } = *fs else {
            panic!("expected ForStmt::Range");
        };
        let body_text = &src[body.span.start..body.span.end];
        assert!(
            !body_text.contains("end"),
            "for-Range body span overshoots into 'end': {body_text:?}"
        );
    }

    /// Anchors the Task-4 fix: `ForStmt::Iter.body.span` ends at the last
    /// consumed statement, not at the closing `end`.
    #[test]
    fn for_iter_body_span_does_not_include_end() {
        let src = "function f(): Int\n  for x in xs do\n    return x\n  end\n  return 0\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let for_stmt = func
            .body
            .stmts
            .iter()
            .find(|s| matches!(s.kind, StmtKind::For(_)))
            .expect("expected For stmt");
        let StmtKind::For(ref fs) = for_stmt.kind else {
            unreachable!()
        };
        let ForStmt::Iter { ref body, .. } = *fs else {
            panic!("expected ForStmt::Iter");
        };
        let body_text = &src[body.span.start..body.span.end];
        assert!(
            !body_text.contains("end"),
            "for-Iter body span overshoots into 'end': {body_text:?}"
        );
    }

    /// Anchors the Task-4 fix: `ForStmt::IterKV.body.span` ends at the last
    /// consumed statement, not at the closing `end`.
    #[test]
    fn for_iterkv_body_span_does_not_include_end() {
        let src = "function f(): Int\n  for k, v in m do\n    return v\n  end\n  return 0\nend\n";
        let toks = tokenize(src).unwrap();
        let mut p = Parser::new(&toks);
        let prog = parse_program(&mut p).unwrap();
        let Item::Function(ref func) = prog.items[0] else {
            panic!("expected Function");
        };
        let for_stmt = func
            .body
            .stmts
            .iter()
            .find(|s| matches!(s.kind, StmtKind::For(_)))
            .expect("expected For stmt");
        let StmtKind::For(ref fs) = for_stmt.kind else {
            unreachable!()
        };
        let ForStmt::IterKV { ref body, .. } = *fs else {
            panic!("expected ForStmt::IterKV");
        };
        let body_text = &src[body.span.start..body.span.end];
        assert!(
            !body_text.contains("end"),
            "for-IterKV body span overshoots into 'end': {body_text:?}"
        );
    }
}
