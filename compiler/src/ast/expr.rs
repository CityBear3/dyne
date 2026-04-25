//! Expression AST nodes.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    IntLit(i64),
    FloatLit(f64),
    StrLit(String),
    BoolLit(bool),
    VecLit(Vec<Expr>),
    MatLit(Vec<Vec<Expr>>),

    Ident(String),

    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnaryOp(UnaryOp, Box<Expr>),

    Call(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    FieldAccess(Box<Expr>, String),

    Lambda(LambdaExpr),
    StructLit(String, Vec<(String, Expr)>),
    If(IfExpr),
    Match(Box<Expr>, Vec<MatchArm>),
    Block(Block),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Pow,
    Eq, Neq, Lt, Gt, Le, Ge,
    And, Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

// Forward declarations from sibling modules:
use crate::ast::stmt::Block;
use crate::ast::item::{LambdaExpr, MatchArm};

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub cond: Box<Expr>,
    pub then_block: Block,
    pub elseifs: Vec<(Expr, Block)>,
    pub else_block: Option<Block>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_int_lit() {
        let e = Expr {
            kind: ExprKind::IntLit(42),
            span: Span::new(0, 2),
        };
        assert_eq!(e.kind, ExprKind::IntLit(42));
    }

    #[test]
    fn construct_binop() {
        let lhs = Expr { kind: ExprKind::IntLit(1), span: Span::new(0, 1) };
        let rhs = Expr { kind: ExprKind::IntLit(2), span: Span::new(4, 5) };
        let e = Expr {
            kind: ExprKind::BinOp(BinOp::Add, Box::new(lhs), Box::new(rhs)),
            span: Span::new(0, 5),
        };
        match e.kind {
            ExprKind::BinOp(BinOp::Add, _, _) => {}
            _ => panic!("expected BinOp::Add"),
        }
    }
}
