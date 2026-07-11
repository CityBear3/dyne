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

/// A `for` loop. Each variant carries parser-minted binding-intro NodeIds for
/// its loop variable(s) (`var_id`, or `key_id` / `value_id` for `IterKV`).
/// These must be unique ids from `Parser::fresh_node_id()`: the resolver keys
/// each loop variable's DefId by its binding NodeId, so reusing a placeholder
/// such as `NodeId(0)` (e.g. in a hand-built AST fixture) silently corrupts
/// `binding_def_ids`.
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
