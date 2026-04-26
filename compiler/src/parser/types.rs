//! Type expression parser.

use crate::ast::{Type, TypeArg, TypeKind, UnitExpr, UnitExprKind};
use crate::error::CompileError;
use crate::lexer::TokenKind;
use crate::parser::Parser;
use crate::source::Span;

pub(crate) fn parse_type(p: &mut Parser) -> Result<Type, CompileError> {
    let start = p.current_span();

    // Function type: Fn(T, ...) -> R
    if let TokenKind::Ident(name) = p.peek_kind()
        && name == "Fn"
    {
        p.advance();
        p.expect(&TokenKind::LParen, "'('")?;
        let mut params = Vec::new();
        if !p.at(&TokenKind::RParen) {
            params.push(parse_type(p)?);
            while p.eat(&TokenKind::Comma) {
                params.push(parse_type(p)?);
            }
        }
        p.expect(&TokenKind::RParen, "')'")?;
        p.expect(&TokenKind::Arrow, "'->'")?;
        let ret = parse_type(p)?;
        let end = ret.span;
        return Ok(Type {
            kind: TypeKind::Function(params, Box::new(ret)),
            span: Span::merge(start, end),
        });
    }

    // Named or Generic
    let ident_tok = p.peek().clone();
    let name = if let TokenKind::Ident(n) = &ident_tok.kind {
        n.clone()
    } else {
        return Err(CompileError::parse(
            ident_tok.span,
            format!("expected type name, found {:?}", ident_tok.kind),
        ));
    };
    p.advance();

    if p.eat(&TokenKind::Lt) {
        let mut args = Vec::new();
        args.push(parse_type_arg(p)?);
        while p.eat(&TokenKind::Comma) {
            args.push(parse_type_arg(p)?);
        }
        let end_tok = p.peek().clone();
        p.expect(&TokenKind::Gt, "'>'")?;
        Ok(Type {
            kind: TypeKind::Generic(name, args),
            span: Span::merge(ident_tok.span, end_tok.span),
        })
    } else {
        Ok(Type {
            kind: TypeKind::Named(name),
            span: ident_tok.span,
        })
    }
}

pub(crate) fn parse_type_param_list(p: &mut Parser) -> Result<Vec<String>, CompileError> {
    if !p.eat(&TokenKind::Lt) {
        return Ok(Vec::new());
    }
    let mut params = Vec::new();
    if !p.at(&TokenKind::Gt) {
        params.push(parse_type_param_name(p)?);
        while p.eat(&TokenKind::Comma) {
            params.push(parse_type_param_name(p)?);
        }
    }
    p.expect(&TokenKind::Gt, "'>'")?;
    Ok(params)
}

fn parse_type_param_name(p: &mut Parser) -> Result<String, CompileError> {
    let tok = p.peek().clone();
    match &tok.kind {
        TokenKind::Ident(n) => {
            p.advance();
            Ok(n.clone())
        }
        _ => Err(CompileError::parse(
            tok.span,
            "expected type parameter name",
        )),
    }
}

fn parse_type_arg(p: &mut Parser) -> Result<TypeArg, CompileError> {
    // Int literal
    if let TokenKind::Int(n) = p.peek_kind() {
        let n = *n;
        p.advance();
        return Ok(TypeArg::Int(n));
    }

    // Unit expression: an Ident followed by `*`, `/`, `^`, or terminator.
    // We detect by looking ahead: if after Ident we see `,`, `>` => it may be a Type or Unit.
    // Disambiguate: treat as Unit if any of `*`, `/`, `^` appears before `,` or `>`;
    // otherwise treat as Type (Named). This covers `kg`, `m/s`, `Scalar`, `Vec<3>` as type args.
    if let TokenKind::Ident(_) = p.peek_kind() {
        let mut look = 1;
        loop {
            match p.peek_ahead(look) {
                TokenKind::Star | TokenKind::Slash | TokenKind::Caret => {
                    return Ok(TypeArg::Unit(parse_unit_expr(p)?));
                }
                TokenKind::Comma | TokenKind::Gt | TokenKind::Eof => break,
                TokenKind::Lt => break, // nested generic => Type
                _ => look += 1,
            }
        }
    }

    // Fallback: parse as Type.
    let t = parse_type(p)?;
    Ok(TypeArg::Type(t))
}

fn parse_unit_expr(p: &mut Parser) -> Result<UnitExpr, CompileError> {
    let mut lhs = parse_unit_factor(p)?;
    loop {
        if p.eat(&TokenKind::Star) {
            let rhs = parse_unit_factor(p)?;
            let span = Span::merge(lhs.span, rhs.span);
            lhs = UnitExpr {
                kind: UnitExprKind::Mul(Box::new(lhs), Box::new(rhs)),
                span,
            };
        } else if p.eat(&TokenKind::Slash) {
            let rhs = parse_unit_factor(p)?;
            let span = Span::merge(lhs.span, rhs.span);
            lhs = UnitExpr {
                kind: UnitExprKind::Div(Box::new(lhs), Box::new(rhs)),
                span,
            };
        } else {
            break;
        }
    }
    Ok(lhs)
}

fn parse_unit_factor(p: &mut Parser) -> Result<UnitExpr, CompileError> {
    let tok = p.peek().clone();
    let atom = match &tok.kind {
        TokenKind::Ident(n) => n.clone(),
        _ => {
            return Err(CompileError::parse(
                tok.span,
                format!("expected unit atom, found {:?}", tok.kind),
            ));
        }
    };
    p.advance();
    let mut expr = UnitExpr {
        kind: UnitExprKind::Atom(atom),
        span: tok.span,
    };
    if p.eat(&TokenKind::Caret) {
        let exp_tok = p.peek().clone();
        let n = match &exp_tok.kind {
            TokenKind::Int(n) => *n,
            _ => {
                return Err(CompileError::parse(
                    exp_tok.span,
                    format!("expected integer exponent, found {:?}", exp_tok.kind),
                ));
            }
        };
        p.advance();
        let span = Span::merge(expr.span, exp_tok.span);
        expr = UnitExpr {
            kind: UnitExprKind::Pow(Box::new(expr), n),
            span,
        };
    }
    Ok(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TypeKind;
    use crate::lexer::tokenize;

    fn parse(source: &str) -> Type {
        let toks = tokenize(source).unwrap();
        let mut p = Parser::new(&toks);
        parse_type(&mut p).unwrap()
    }

    #[test]
    fn named_type() {
        let t = parse("Scalar");
        assert!(matches!(t.kind, TypeKind::Named(ref n) if n == "Scalar"));
    }

    #[test]
    fn vec_with_int_arg() {
        let t = parse("Vec<3>");
        if let TypeKind::Generic(name, args) = t.kind {
            assert_eq!(name, "Vec");
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], crate::ast::TypeArg::Int(3)));
        } else {
            panic!("expected Generic");
        }
    }

    #[test]
    fn mat_with_two_ints() {
        let t = parse("Mat<2, 3>");
        if let TypeKind::Generic(name, args) = t.kind {
            assert_eq!(name, "Mat");
            assert_eq!(args.len(), 2);
        } else {
            panic!("expected Generic");
        }
    }

    #[test]
    fn scalar_with_simple_unit() {
        let t = parse("Scalar<kg>");
        if let TypeKind::Generic(name, args) = t.kind {
            assert_eq!(name, "Scalar");
            assert_eq!(args.len(), 1);
            match &args[0] {
                crate::ast::TypeArg::Type(inner) => {
                    assert!(matches!(inner.kind, TypeKind::Named(ref n) if n == "kg"));
                }
                _ => panic!("expected Type for bare ident, got {:?}", args[0]),
            }
        } else {
            panic!("expected Generic");
        }
    }

    #[test]
    fn scalar_with_compound_unit() {
        // kg*m/s^2
        let t = parse("Scalar<kg*m/s^2>");
        if let TypeKind::Generic(name, args) = t.kind {
            assert_eq!(name, "Scalar");
            assert!(matches!(args[0], crate::ast::TypeArg::Unit(_)));
        } else {
            panic!("expected Generic");
        }
    }

    #[test]
    fn vec_with_unit() {
        let t = parse("Vec<3, m/s>");
        if let TypeKind::Generic(_, args) = t.kind {
            assert_eq!(args.len(), 2);
            assert!(matches!(args[0], crate::ast::TypeArg::Int(3)));
            assert!(matches!(args[1], crate::ast::TypeArg::Unit(_)));
        }
    }

    #[test]
    fn function_type() {
        let t = parse("Fn(Scalar, Scalar) -> Scalar");
        if let TypeKind::Function(params, ret) = t.kind {
            assert_eq!(params.len(), 2);
            assert!(matches!(ret.kind, TypeKind::Named(ref n) if n == "Scalar"));
        } else {
            panic!("expected Function");
        }
    }
}
