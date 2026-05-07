//! Type representation for the sema phase.
//!
//! Populated incrementally through Stage 3:
//! - PR-3b: `Ty` enum, `Dimension` stub (ZERO only), `TypeVarId`, `lower_type`
//! - PR-3d: `Dimension` arithmetic (mul, div, pow), unit propagation through operators
//! - PR-3c: enum type-argument instantiation via `TypeVarId`

use crate::ast::{Type, TypeArg, TypeKind};
use crate::diag::Diagnostic;
use crate::ids::DefId;
use crate::sema::resolve::{DefKind, DefinitionTable, ResolveTable};
use crate::source::Span;

/// Internal type representation. Keys into the `TypeTable` for expressions
/// and the `def_types` / `struct_fields` / `variant_payloads` tables for
/// definitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Int,
    Scalar(Dimension),
    Bool,
    String,
    /// `Vec<N, unit>` — fixed length N, element unit Dimension.
    Vec(usize, Dimension),
    /// `Mat<M, N>` — rows × cols. Always dimensionless per spec §4.4.
    Mat(usize, usize),
    Array(Box<Ty>),
    Dict(Box<Ty>, Box<Ty>),
    /// Function: parameter types + return type.
    Function(Vec<Ty>, Box<Ty>),
    /// User-defined struct, identified by its DefId.
    Struct(DefId),
    /// User-defined enum + (instantiated) type arguments. PR-3b stores
    /// non-generic enums (empty Vec). PR-3c populates the Vec for generic
    /// instantiations.
    Enum(DefId, Vec<Ty>),
    /// Unification variable (introduced by match arm unification in 3b,
    /// enum constructor inference in 3c).
    Var(TypeVarId),
    /// Sentinel for nodes whose type could not be determined due to a
    /// previous diagnostic. Compatible with any expected type to suppress
    /// cascading errors.
    Error,
}

/// Integer dimension vector over the seven SI base dimensions:
/// [length, mass, time, current, temperature, amount, luminous].
///
/// PR-3b only uses `Dimension::ZERO` (dimensionless). PR-3d will populate
/// the inner `i8` array, add `mul`/`div`/`pow`/`is_dimensionless`/`format_si`
/// methods, and replace `ZERO` placeholders in operator rules.
///
/// The inner array is private — future migration to rational exponents
/// (PR-3? — noise spectroscopy use cases) is local to this module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dimension([i8; 7]);

impl Dimension {
    pub const ZERO: Self = Self([0; 7]);

    /// Returns true iff this dimension is the dimensionless `ZERO`.
    pub fn is_dimensionless(self) -> bool {
        self == Self::ZERO
    }
}

/// Index into a unification table. Allocated by `unify::Table::fresh()`
/// (added in Task 6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub u32);

/// Stored per enum-variant DefId in `TypedProgram::variant_payloads`.
/// Pairs the parent enum's DefId with the lowered payload types so a
/// downstream walk can recover the variant's parent and arity in one
/// lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantPayload {
    pub parent_enum: DefId,
    pub payload: Vec<Ty>,
}

/// Lower an AST `Type` to an internal `Ty`.
///
/// Diagnostics are accumulated; on any error, returns `Ty::Error` for the
/// offending sub-tree but continues lowering the remainder so multiple
/// type-annotation errors surface in a single compile.
pub fn lower_type(
    ast_ty: &Type,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match &ast_ty.kind {
        TypeKind::Named(name) => match name.as_str() {
            "Int" => Ty::Int,
            "Bool" => Ty::Bool,
            "String" => Ty::String,
            "Scalar" => Ty::Scalar(Dimension::ZERO),
            "Vec" | "Mat" | "Array" | "Dict" => {
                // Without args these don't have valid Ty representations;
                // they need at least one type/int parameter.
                diags.push(Diagnostic::type_error(
                    ast_ty.span,
                    format!("`{name}` requires type arguments (e.g. `{name}<3>`)"),
                ));
                Ty::Error
            }
            _ => lower_user_named(name, ast_ty, resolutions, definitions, diags),
        },
        TypeKind::Generic(name, args) => match name.as_str() {
            "Scalar" => lower_scalar(args, ast_ty.span, diags),
            "Vec" => lower_vec(args, ast_ty.span, diags),
            "Mat" => lower_mat(args, ast_ty.span, diags),
            "Array" => lower_array(args, ast_ty.span, resolutions, definitions, diags),
            "Dict" => lower_dict(args, ast_ty.span, resolutions, definitions, diags),
            _ => {
                // User-defined generic instantiation: deferred to PR-3c.
                diags.push(Diagnostic::type_error(
                    ast_ty.span,
                    format!(
                        "generic enum instantiation not yet supported (PR-3c will land `{name}<...>`)"
                    ),
                ));
                Ty::Error
            }
        },
        TypeKind::Function(args, ret) => {
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|a| lower_type(a, resolutions, definitions, diags))
                .collect();
            let ret_ty = lower_type(ret, resolutions, definitions, diags);
            Ty::Function(arg_tys, Box::new(ret_ty))
        }
    }
}

fn lower_user_named(
    name: &str,
    ast_ty: &Type,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    let Some(def_id) = resolutions.get(&ast_ty.id).copied() else {
        // Resolver should have produced a diag already; emit a Ty::Error
        // sentinel without an additional diag.
        return Ty::Error;
    };
    match definitions.get(&def_id).map(|info| info.kind) {
        Some(DefKind::Struct) => Ty::Struct(def_id),
        Some(DefKind::Enum) => Ty::Enum(def_id, Vec::new()),
        Some(_) => {
            diags.push(Diagnostic::type_error(
                ast_ty.span,
                format!("`{name}` is not a type"),
            ));
            Ty::Error
        }
        None => Ty::Error,
    }
}

/// `Scalar` / `Scalar<unit>` → `Ty::Scalar(Dimension::ZERO)`. Per Option β,
/// any unit argument is silently stripped (PR-3d will replace ZERO with the
/// actual dimension vector).
fn lower_scalar(args: &[TypeArg], span: Span, diags: &mut Vec<Diagnostic>) -> Ty {
    match args {
        [] => Ty::Scalar(Dimension::ZERO),
        // Single-atom units may be parsed as TypeArg::Type(Named("kg")); the
        // resolver doesn't distinguish them from real types, so accept either
        // shape here without recording a unit.
        [TypeArg::Unit(_)] | [TypeArg::Type(_)] => Ty::Scalar(Dimension::ZERO),
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Scalar` accepts at most one unit argument",
            ));
            Ty::Error
        }
    }
}

/// `Vec<N>` or `Vec<N, unit>` → `Ty::Vec(N, ZERO)`. N must be a positive `IntLit`.
/// The optional second arg is silently stripped per Option β.
fn lower_vec(args: &[TypeArg], span: Span, diags: &mut Vec<Diagnostic>) -> Ty {
    let n = match args.first() {
        Some(TypeArg::Int(n)) if *n > 0 => *n as usize,
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Vec` requires a positive integer size as its first argument",
            ));
            return Ty::Error;
        }
    };
    if args.len() > 2 {
        diags.push(Diagnostic::type_error(
            span,
            "`Vec` accepts at most a size and an optional unit argument",
        ));
        return Ty::Error;
    }
    Ty::Vec(n, Dimension::ZERO)
}

/// `Mat<M, N>` → `Ty::Mat(M, N)`. Both args are positive `IntLit`. Spec §4.4
/// says matrices are dimensionless.
fn lower_mat(args: &[TypeArg], span: Span, diags: &mut Vec<Diagnostic>) -> Ty {
    match args {
        [TypeArg::Int(m), TypeArg::Int(n)] if *m > 0 && *n > 0 => Ty::Mat(*m as usize, *n as usize),
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Mat` requires two positive integer dimensions (e.g. `Mat<3, 4>`)",
            ));
            Ty::Error
        }
    }
}

/// `Array<T>` → `Ty::Array(T)`.
fn lower_array(
    args: &[TypeArg],
    span: Span,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match args {
        [TypeArg::Type(t)] => Ty::Array(Box::new(lower_type(t, resolutions, definitions, diags))),
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Array` requires exactly one type argument",
            ));
            Ty::Error
        }
    }
}

/// `Dict<K, V>` → `Ty::Dict(K, V)`.
fn lower_dict(
    args: &[TypeArg],
    span: Span,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match args {
        [TypeArg::Type(k), TypeArg::Type(v)] => Ty::Dict(
            Box::new(lower_type(k, resolutions, definitions, diags)),
            Box::new(lower_type(v, resolutions, definitions, diags)),
        ),
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Dict` requires exactly two type arguments (key, value)",
            ));
            Ty::Error
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::Diagnostic;
    use crate::lexer::tokenize;
    use crate::parser::parse;
    use crate::sema::resolve::resolve_program;

    fn lower_first_let_ty(src: &str) -> (Ty, Vec<Diagnostic>) {
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[0];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        (ty, diags)
    }

    #[test]
    fn lower_int_returns_ty_int() {
        let (ty, diags) = lower_first_let_ty("let x: Int = 0");
        assert_eq!(ty, Ty::Int);
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_bool_returns_ty_bool() {
        let (ty, _) = lower_first_let_ty("let x: Bool = true");
        assert_eq!(ty, Ty::Bool);
    }

    #[test]
    fn lower_string_returns_ty_string() {
        let (ty, _) = lower_first_let_ty("let x: String = \"hi\"");
        assert_eq!(ty, Ty::String);
    }

    #[test]
    fn lower_scalar_no_args_is_zero_dimension() {
        let (ty, _) = lower_first_let_ty("let x: Scalar = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension::ZERO));
    }

    #[test]
    fn lower_scalar_with_unit_silently_strips() {
        // Option β: `Scalar<kg>` → Ty::Scalar(ZERO), no diagnostic.
        let (ty, diags) = lower_first_let_ty("let x: Scalar<kg> = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension::ZERO));
        assert!(
            diags.is_empty(),
            "expected silent strip, got diags: {:?}",
            diags
        );
    }

    #[test]
    fn lower_vec_with_size_and_no_unit() {
        let (ty, _) = lower_first_let_ty("let v: Vec<3> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension::ZERO));
    }

    #[test]
    fn lower_mat_with_two_sizes() {
        let (ty, _) = lower_first_let_ty("let m: Mat<3, 4> = 0");
        assert_eq!(ty, Ty::Mat(3, 4));
    }

    #[test]
    fn lower_array_of_int() {
        let (ty, _) = lower_first_let_ty("let xs: Array<Int> = 0");
        assert_eq!(ty, Ty::Array(Box::new(Ty::Int)));
    }

    #[test]
    fn lower_dict_int_string() {
        let (ty, _) = lower_first_let_ty("let d: Dict<Int, String> = 0");
        assert_eq!(ty, Ty::Dict(Box::new(Ty::Int), Box::new(Ty::String)));
    }

    #[test]
    fn lower_user_struct_returns_struct_def_id() {
        let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let p_let = &prog.items[1];
        let ty = match p_let {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!(),
        };
        assert!(matches!(ty, Ty::Struct(_)));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_generic_enum_user_defined_is_deferred_to_3c() {
        // `Result<Int, String>` — user-defined generic instantiation is 3c.
        let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nlet r: Result<Int, String> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let r_let = &prog.items[1];
        let ty = match r_let {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!(),
        };
        assert_eq!(ty, Ty::Error);
        assert!(diags.iter().any(|d| d.message.contains("PR-3c")));
    }
}
