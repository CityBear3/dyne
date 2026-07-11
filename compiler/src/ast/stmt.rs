//! Statement AST nodes.

use crate::ast::expr::Expr;
use crate::ast::ty::Type;
use crate::ids::NodeId;
use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
    pub id: NodeId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub id: NodeId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    Let(LetStmt),
    Assign(String, Expr),
    Expr(Expr),
    Return(Option<Expr>),
    For(ForStmt),
    While(WhileStmt),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetStmt {
    pub name: String,
    pub ty: Type,
    pub init: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ForStmt {
    Range {
        var: String,
        /// Binding-intro NodeId for `var`, minted by the parser.
        var_id: NodeId,
        start: Expr,
        end: Expr,
        body: Block,
    },
    Iter {
        var: String,
        /// Binding-intro NodeId for `var`, minted by the parser.
        var_id: NodeId,
        iter: Expr,
        body: Block,
    },
    IterKV {
        key: String,
        /// Binding-intro NodeId for `key`, minted by the parser.
        key_id: NodeId,
        value: String,
        /// Binding-intro NodeId for `value`, minted by the parser.
        value_id: NodeId,
        iter: Expr,
        body: Block,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub cond: Expr,
    pub body: Block,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::expr::ExprKind;
    use crate::ast::ty::{Type, TypeKind};

    #[test]
    fn construct_let_stmt() {
        let stmt = Stmt {
            kind: StmtKind::Let(LetStmt {
                name: "x".into(),
                ty: Type {
                    kind: TypeKind::Named("Scalar".into()),
                    span: Span::new(0, 6),
                    id: NodeId(0),
                },
                init: Expr {
                    kind: ExprKind::FloatLit(1.0),
                    span: Span::new(10, 13),
                    id: NodeId(0),
                },
            }),
            span: Span::new(0, 13),
            id: NodeId(0),
        };
        if let StmtKind::Let(l) = &stmt.kind {
            assert_eq!(l.name, "x");
        } else {
            panic!("expected Let");
        }
    }
}
