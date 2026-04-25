//! Type AST nodes.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Named(String),
    Generic(String, Vec<TypeArg>),
    Function(Vec<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeArg {
    Type(Type),
    Int(i64),
    Unit(UnitExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnitExpr {
    pub kind: UnitExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnitExprKind {
    Atom(String),
    Mul(Box<UnitExpr>, Box<UnitExpr>),
    Div(Box<UnitExpr>, Box<UnitExpr>),
    Pow(Box<UnitExpr>, i64),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_scalar() {
        let t = Type {
            kind: TypeKind::Named("Scalar".into()),
            span: Span::new(0, 6),
        };
        assert!(matches!(t.kind, TypeKind::Named(ref n) if n == "Scalar"));
    }

    #[test]
    fn vec3_generic() {
        let t = Type {
            kind: TypeKind::Generic(
                "Vec".into(),
                vec![TypeArg::Int(3)],
            ),
            span: Span::new(0, 6),
        };
        if let TypeKind::Generic(name, args) = &t.kind {
            assert_eq!(name, "Vec");
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], TypeArg::Int(3)));
        }
    }

    #[test]
    fn scalar_with_unit() {
        let unit = UnitExpr {
            kind: UnitExprKind::Atom("kg".into()),
            span: Span::new(7, 9),
        };
        let t = Type {
            kind: TypeKind::Generic(
                "Scalar".into(),
                vec![TypeArg::Unit(unit)],
            ),
            span: Span::new(0, 10),
        };
        if let TypeKind::Generic(name, args) = &t.kind {
            assert_eq!(name, "Scalar");
            assert!(matches!(args[0], TypeArg::Unit(_)));
        }
    }
}
