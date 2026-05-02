//! Top-level items and their supporting types.

use crate::ast::expr::Expr;
use crate::ast::stmt::{Block, LetStmt};
use crate::ast::ty::Type;
use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Import(ImportItem),
    Function(FunctionDef),
    Let(LetStmt),
    Struct(StructDef),
    Enum(EnumDef),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImportItem {
    pub path: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<Param>,
    pub return_ty: Type,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub params: Vec<Param>,
    pub return_ty: Option<Type>,
    pub body: LambdaBody,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LambdaBody {
    Expr(Box<Expr>),
    Block(Block),
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<StructField>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub payload: Vec<Type>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    Wildcard,
    Ident(String),
    Variant(String, Vec<Pattern>),
    IntLit(i64),
    BoolLit(bool),
    StrLit(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_program() {
        let p = Program {
            items: vec![],
            span: Span::new(0, 0),
        };
        assert_eq!(p.items.len(), 0);
    }

    #[test]
    fn pattern_literal_variants_distinct_and_typed() {
        assert_eq!(PatternKind::IntLit(42), PatternKind::IntLit(42));
        assert_ne!(PatternKind::IntLit(42), PatternKind::IntLit(0));
        assert_ne!(PatternKind::BoolLit(true), PatternKind::BoolLit(false));
        assert_ne!(PatternKind::IntLit(1), PatternKind::BoolLit(true));
        assert_eq!(
            PatternKind::StrLit("hello".into()),
            PatternKind::StrLit("hello".into()),
        );
        assert_ne!(
            PatternKind::StrLit("a".into()),
            PatternKind::StrLit("b".into()),
        );
    }

    #[test]
    fn enum_with_variants() {
        let e = EnumDef {
            name: "Option".into(),
            type_params: vec!["T".into()],
            variants: vec![
                EnumVariant {
                    name: "Some".into(),
                    payload: vec![],
                    span: Span::new(0, 4),
                },
                EnumVariant {
                    name: "None".into(),
                    payload: vec![],
                    span: Span::new(5, 9),
                },
            ],
            span: Span::new(0, 10),
        };
        assert_eq!(e.variants.len(), 2);
    }
}
