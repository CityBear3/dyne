//! Type representation for the sema phase.
//!
//! Populated incrementally through Stage 3:
//! - PR-3b: `Ty` enum, `Dimension` stub (ZERO only), `TypeVarId`, `lower_type`
//! - PR-3d: `Dimension` arithmetic (mul, div, pow), unit propagation through operators
//! - PR-3c: enum type-argument instantiation via `TypeVarId`

use std::collections::HashMap;

use crate::ast::{Type, TypeArg, TypeKind};
use crate::diag::Diagnostic;
use crate::ids::DefId;
use crate::sema::resolve::{DefKind, DefinitionTable, ResolveTable};
use crate::source::Span;

/// Substitution map from a parent definition's type-parameter name to its
/// schema index. `lower_type_with_subst` returns `Ty::Param(i)` whenever a
/// `TypeKind::Named(name)` matches a key. Used by `signature_pass` to lower
/// variant payloads inside generic enums (and by future stdlib-generic
/// signatures).
pub(crate) type ParamSubst<'a> = HashMap<&'a str, usize>;

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
    /// Type-parameter sentinel. Indexed by position in the parent definition's
    /// `type_params` list. Stored only in `def_types` / `variant_payloads`
    /// schemas; substituted with fresh `Var` at each use site by `synth_ident`
    /// (Task 4). Should not appear in expression types written to
    /// `TypedProgram.types` after PR-3c lands.
    Param(usize),
    /// Sentinel for nodes whose type could not be determined due to a
    /// previous diagnostic. Compatible with any expected type to suppress
    /// cascading errors.
    Error,
}

/// Integer dimension vector over the seven SI base dimensions:
/// [length, mass, time, current, temperature, amount, luminous].
///
/// PR-3b only uses `Dimension::ZERO` (dimensionless). PR-3d populates
/// the inner `i8` array via `mul`/`div`/`pow` arithmetic and the
/// `UnitRegistry` lookup table; `format_si` renders the canonical SI
/// base form for diagnostics.
///
/// The inner array is `pub(crate)` — accessible to crate-internal
/// callers (`UnitRegistry::lookup`, sema tests) but NOT exposed in the
/// external `dyne::sema::ty` API surface. Future migration to rational
/// exponents (PR-3? — noise spectroscopy use cases) stays scoped to
/// the crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dimension(pub(crate) [i8; 7]);

/// Symbol for each SI base dimension, indexed parallel to `Dimension`'s
/// inner array: [length, mass, time, current, temperature, amount, luminous].
const BASE_NAMES: [&str; 7] = ["m", "kg", "s", "A", "K", "mol", "cd"];

impl Dimension {
    pub const ZERO: Self = Self([0; 7]);

    /// Returns true iff this dimension is the dimensionless `ZERO`.
    pub fn is_dimensionless(self) -> bool {
        self == Self::ZERO
    }

    /// Renders the canonical SI base form as ASCII. Examples:
    ///   ZERO              → "1"
    ///   [1, 0, ...]       → "m"
    ///   [1, 1, -2, ...]   → "m*kg*s^-2"
    /// Negative exponents render as `name^-n`. Exponent of 1 elides.
    /// Order is fixed: m, kg, s, A, K, mol, cd.
    pub fn format_si(self) -> String {
        if self.is_dimensionless() {
            return "1".to_string();
        }
        let mut parts = Vec::new();
        for (i, &exp) in self.0.iter().enumerate() {
            if exp == 0 {
                continue;
            }
            if exp == 1 {
                parts.push(BASE_NAMES[i].to_string());
            } else {
                parts.push(format!("{}^{}", BASE_NAMES[i], exp));
            }
        }
        parts.join("*")
    }
}

impl std::fmt::Display for Dimension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.format_si())
    }
}

/// Reported by `Dimension::mul` / `div` / `pow` when an i8 element would
/// overflow during the operation. Sites that compute dimensions push
/// `dimension_overflow` diagnostics and substitute `Dimension::ZERO` to
/// suppress cascade.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverflowError;

impl Dimension {
    /// Pointwise add: each element of `self` and `other` are added with
    /// checked i8 arithmetic. Returns `Err(OverflowError)` if any element
    /// overflows i8 (`i8::MIN..=i8::MAX`).
    //
    // Name matches the unit-algebra domain (multiplying two unit vectors =
    // pointwise add of exponents, e.g. `kg * m/s = kg*m/s`). Not the
    // numeric `std::ops::Mul`, hence the allow.
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: Self) -> Result<Self, OverflowError> {
        self.pointwise(other, i8::checked_add)
    }

    /// Pointwise subtract.
    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: Self) -> Result<Self, OverflowError> {
        self.pointwise(other, i8::checked_sub)
    }

    /// Pointwise multiply by integer exponent. `pow(self, n)` produces a
    /// dimension where each element is `self[i] * n`. Returns Err on i8
    /// overflow.
    pub fn pow(self, n: i8) -> Result<Self, OverflowError> {
        let mut out = [0i8; 7];
        for (dst, &a) in out.iter_mut().zip(&self.0) {
            *dst = a.checked_mul(n).ok_or(OverflowError)?;
        }
        Ok(Self(out))
    }

    fn pointwise(self, other: Self, op: fn(i8, i8) -> Option<i8>) -> Result<Self, OverflowError> {
        let mut out = [0i8; 7];
        for (dst, (&a, &b)) in out.iter_mut().zip(self.0.iter().zip(&other.0)) {
            *dst = op(a, b).ok_or(OverflowError)?;
        }
        Ok(Self(out))
    }
}

/// Static built-in unit registry. Maps unit names to canonical
/// `Dimension` values. Per /design-discussion 2026-05-08 Q3, scope is
/// SI base 7 + 8 derived units. SI prefixes (km, ms, μs), CGS (cm, g),
/// and scale-factor folding are deferred to PR-3e or later.
pub(crate) struct UnitRegistry;

impl UnitRegistry {
    /// Look up a unit name. Returns `Some(dim)` for known units,
    /// `None` for unknown — caller emits `unknown_unit` diagnostic.
    pub(crate) fn lookup(name: &str) -> Option<Dimension> {
        match name {
            // SI base units
            "m" => Some(Dimension([1, 0, 0, 0, 0, 0, 0])),
            "kg" => Some(Dimension([0, 1, 0, 0, 0, 0, 0])),
            "s" => Some(Dimension([0, 0, 1, 0, 0, 0, 0])),
            "A" => Some(Dimension([0, 0, 0, 1, 0, 0, 0])),
            "K" => Some(Dimension([0, 0, 0, 0, 1, 0, 0])),
            "mol" => Some(Dimension([0, 0, 0, 0, 0, 1, 0])),
            "cd" => Some(Dimension([0, 0, 0, 0, 0, 0, 1])),
            // SI derived units (in canonical base form)
            "N" => Some(Dimension([1, 1, -2, 0, 0, 0, 0])), // kg*m/s^2
            "J" => Some(Dimension([2, 1, -2, 0, 0, 0, 0])), // N*m = kg*m^2/s^2
            "W" => Some(Dimension([2, 1, -3, 0, 0, 0, 0])), // J/s
            "Pa" => Some(Dimension([-1, 1, -2, 0, 0, 0, 0])), // N/m^2
            "Hz" => Some(Dimension([0, 0, -1, 0, 0, 0, 0])), // 1/s
            "C" => Some(Dimension([0, 0, 1, 1, 0, 0, 0])),  // A*s
            "V" => Some(Dimension([2, 1, -3, -1, 0, 0, 0])), // W/A = kg*m^2/(s^3*A)
            "Ω" => Some(Dimension([2, 1, -3, -2, 0, 0, 0])), // V/A
            _ => None,
        }
    }
}

/// Evaluate a `UnitExpr` AST node to a `Dimension` value. Recursively
/// walks Atom / Mul / Div / Pow nodes. Emits diagnostics on unknown
/// unit names, exponents outside i8 range, and dimension-component
/// overflow. Returns `Dimension::ZERO` as cascade-suppression sentinel
/// on any error so subsequent type checking continues.
pub(crate) fn eval_unit_expr(u: &crate::ast::UnitExpr, diags: &mut Vec<Diagnostic>) -> Dimension {
    use crate::ast::UnitExprKind;
    match &u.kind {
        UnitExprKind::Atom(name) => UnitRegistry::lookup(name).unwrap_or_else(|| {
            diags.push(crate::sema::diag::unknown_unit(u.span, name));
            Dimension::ZERO
        }),
        UnitExprKind::Mul(a, b) => {
            let l = eval_unit_expr(a, diags);
            let r = eval_unit_expr(b, diags);
            l.mul(r).unwrap_or_else(|_| {
                diags.push(crate::sema::diag::dimension_overflow(u.span));
                Dimension::ZERO
            })
        }
        UnitExprKind::Div(a, b) => {
            let l = eval_unit_expr(a, diags);
            let r = eval_unit_expr(b, diags);
            l.div(r).unwrap_or_else(|_| {
                diags.push(crate::sema::diag::dimension_overflow(u.span));
                Dimension::ZERO
            })
        }
        UnitExprKind::Pow(base, n) => {
            // Parser produces i64; narrow to i8 with explicit range check
            // before calling Dimension::pow (which itself may still overflow
            // when the base has large exponents).
            if *n < i8::MIN as i64 || *n > i8::MAX as i64 {
                diags.push(crate::sema::diag::unit_exponent_out_of_range(u.span, *n));
                return Dimension::ZERO;
            }
            let base_dim = eval_unit_expr(base, diags);
            base_dim.pow(*n as i8).unwrap_or_else(|_| {
                diags.push(crate::sema::diag::dimension_overflow(u.span));
                Dimension::ZERO
            })
        }
    }
}

/// Index into a unification table. Allocated by `unify::Table::fresh()`
/// — that's the only legitimate constructor, so the inner index is
/// `pub(crate)` rather than `pub`. External consumers can match on
/// `Ty::Var(_)` but cannot fabricate or inspect indices.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub(crate) u32);

/// Stored per enum-variant DefId in `TypedProgram::variant_payloads`.
/// Pairs the parent enum's DefId with the lowered payload types so a
/// downstream walk can recover the variant's parent and arity in one
/// lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantPayload {
    pub parent_enum: DefId,
    pub payload: Vec<Ty>,
}

impl Ty {
    /// Substitute every `Ty::Param(i)` in `self` with `type_args[i]`.
    ///
    /// Used in two places:
    ///   - Task 4 (`synth_ident`): build `type_args` as fresh `Ty::Var`s
    ///     so each variant-constructor use site gets independent inference
    ///     variables. `Some(1)` and `Some("x")` in the same function then
    ///     infer to different `Maybe<Int>` / `Maybe<String>`.
    ///   - Task 5 (`check_pattern`): build `type_args` from the resolved
    ///     scrutinee's enum arguments so a `case Some(x) then ...` pattern
    ///     binds `x` to the concrete payload type, not `Param(0)`.
    ///
    /// `Param(i)` with `i >= type_args.len()` returns `Ty::Error` rather
    /// than panicking — the schema/args mismatch indicates a sema bug
    /// upstream, and Error suppresses cascade.
    pub(crate) fn subst_with_args(&self, type_args: &[Ty]) -> Ty {
        match self {
            Ty::Param(i) => type_args.get(*i).cloned().unwrap_or(Ty::Error),
            Ty::Int
            | Ty::Bool
            | Ty::String
            | Ty::Scalar(_)
            | Ty::Mat(_, _)
            | Ty::Vec(_, _)
            | Ty::Struct(_)
            | Ty::Var(_)
            | Ty::Error => self.clone(),
            Ty::Array(t) => Ty::Array(Box::new(t.subst_with_args(type_args))),
            Ty::Dict(k, v) => Ty::Dict(
                Box::new(k.subst_with_args(type_args)),
                Box::new(v.subst_with_args(type_args)),
            ),
            Ty::Function(args, ret) => Ty::Function(
                args.iter().map(|a| a.subst_with_args(type_args)).collect(),
                Box::new(ret.subst_with_args(type_args)),
            ),
            Ty::Enum(def, args) => Ty::Enum(
                *def,
                args.iter().map(|a| a.subst_with_args(type_args)).collect(),
            ),
        }
    }
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
    lower_type_inner(ast_ty, resolutions, definitions, None, diags)
}

/// Lower an AST `Type` with a type-parameter substitution map. A
/// `TypeKind::Named(name)` matching a key in `subst` returns `Ty::Param(i)`;
/// everything else lowers identically to `lower_type`. Used by
/// `signature_pass` to build variant signature schemas inside generic enums.
pub(crate) fn lower_type_with_subst(
    ast_ty: &Type,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    subst: &ParamSubst<'_>,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    lower_type_inner(ast_ty, resolutions, definitions, Some(subst), diags)
}

fn lower_type_inner(
    ast_ty: &Type,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    subst: Option<&ParamSubst<'_>>,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match &ast_ty.kind {
        TypeKind::Named(name) => {
            // Type-parameter substitution beats every other interpretation:
            // a name listed in the parent definition's `type_params` is a
            // schema sentinel, not a builtin or user-defined type. In
            // practice users won't shadow `Int`/`Bool`, but the schema
            // model says Param wins when there's a collision.
            if let Some(s) = subst
                && let Some(&i) = s.get(name.as_str())
            {
                return Ty::Param(i);
            }
            match name.as_str() {
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
            }
        }
        TypeKind::Generic(name, args) => match name.as_str() {
            "Scalar" => lower_scalar(args, ast_ty.span, diags),
            "Vec" => lower_vec(args, ast_ty.span, diags),
            "Mat" => lower_mat(args, ast_ty.span, diags),
            "Array" => lower_array(args, ast_ty.span, resolutions, definitions, subst, diags),
            "Dict" => lower_dict(args, ast_ty.span, resolutions, definitions, subst, diags),
            _ => lower_user_generic(name, args, ast_ty, resolutions, definitions, subst, diags),
        },
        TypeKind::Function(args, ret) => {
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|a| lower_type_inner(a, resolutions, definitions, subst, diags))
                .collect();
            let ret_ty = lower_type_inner(ret, resolutions, definitions, subst, diags);
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

/// Lower a user-defined generic enum instantiation, e.g. `Result<Int, String>`
/// → `Ty::Enum(result_def, [Int, String])`. The arity of the type-argument list
/// must match the enum's declared `type_params`; non-enum definitions are
/// rejected with a focused "not a generic type" diagnostic. `subst` carries
/// the parent enum's type-parameter mapping for nested cases like
/// `Wrap(Result<T, String>)` inside `enum WrappedResult<T>`.
fn lower_user_generic(
    name: &str,
    args: &[TypeArg],
    ast_ty: &Type,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    subst: Option<&ParamSubst<'_>>,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    let Some(def_id) = resolutions.get(&ast_ty.id).copied() else {
        // Resolver already reported the unknown name; suppress cascade.
        return Ty::Error;
    };
    let Some(info) = definitions.get(&def_id) else {
        return Ty::Error;
    };
    if !matches!(info.kind, DefKind::Enum) {
        diags.push(Diagnostic::type_error(
            ast_ty.span,
            format!("`{name}` is not a generic type"),
        ));
        return Ty::Error;
    }
    let expected = expected_type_param_count(def_id, definitions);
    let actual = args.len();
    if expected != actual {
        diags.push(crate::sema::diag::wrong_type_arity(
            ast_ty.span,
            name,
            expected,
            actual,
        ));
        return Ty::Error;
    }
    let mut lowered_args = Vec::with_capacity(args.len());
    for arg in args {
        let ty = match arg {
            TypeArg::Type(t) => lower_type_inner(t, resolutions, definitions, subst, diags),
            // Generic enums take type arguments only — int literals (Vec<3>)
            // and unit atoms (Scalar<kg>) are reserved for the built-in
            // generic-shaped types handled in their own arms above.
            TypeArg::Int(_) | TypeArg::Unit(_) => {
                diags.push(Diagnostic::type_error(
                    ast_ty.span,
                    format!("`{name}` type arguments must be types, not int/unit literals"),
                ));
                Ty::Error
            }
        };
        lowered_args.push(ty);
    }
    Ty::Enum(def_id, lowered_args)
}

/// Number of type parameters declared on a definition. Returns 0 for
/// definitions that are not generic (or that don't exist). Centralized so
/// future passes don't reach into `DefinitionInfo.type_params` directly.
pub(crate) fn expected_type_param_count(def_id: DefId, definitions: &DefinitionTable) -> usize {
    definitions
        .get(&def_id)
        .map(|info| info.type_params.len())
        .unwrap_or(0)
}

/// `Scalar` / `Scalar<unit>` → `Ty::Scalar(dim)` with `dim` evaluated from
/// the unit annotation. Bare `Scalar` (no args) is dimensionless. On unknown
/// unit / overflow / out-of-range exponent, `eval_unit_expr` emits a focused
/// diag and substitutes `Dimension::ZERO` to suppress cascade.
fn lower_scalar(args: &[TypeArg], span: Span, diags: &mut Vec<Diagnostic>) -> Ty {
    match args {
        [] => Ty::Scalar(Dimension::ZERO),
        [TypeArg::Unit(u)] => Ty::Scalar(eval_unit_expr(u, diags)),
        // Single-atom units (`Scalar<kg>`) parse as TypeArg::Type(Named(...))
        // because the type-arg parser can't tell `kg` apart from `Int` until
        // it sees a `*`/`/`/`^`. Synthesize an Atom UnitExpr so the same
        // unknown_unit / overflow / out-of-range diags apply uniformly.
        [TypeArg::Type(t)] => match &t.kind {
            TypeKind::Named(name) => {
                Ty::Scalar(eval_unit_expr(&synthesize_atom_unit_expr(t, name), diags))
            }
            _ => {
                diags.push(Diagnostic::type_error(
                    span,
                    "`Scalar` accepts a unit expression as its argument",
                ));
                Ty::Error
            }
        },
        _ => {
            diags.push(Diagnostic::type_error(
                span,
                "`Scalar` accepts at most one unit argument",
            ));
            Ty::Error
        }
    }
}

/// `Vec<N>` / `Vec<N, unit>` → `Ty::Vec(N, dim)`. N must be a positive
/// `IntLit`; the optional second arg is evaluated as a unit (same code
/// path and diags as `Scalar<unit>`).
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
    let dim = match args.get(1) {
        None => Dimension::ZERO,
        Some(TypeArg::Unit(u)) => eval_unit_expr(u, diags),
        Some(TypeArg::Type(t)) => match &t.kind {
            TypeKind::Named(name) => eval_unit_expr(&synthesize_atom_unit_expr(t, name), diags),
            // Non-named type in unit position: cascade-suppress to ZERO.
            // The parser is unlikely to produce this shape; Type::Function /
            // Type::Generic in this position would be a parser bug, not a
            // user error worth a custom diag.
            _ => Dimension::ZERO,
        },
        Some(TypeArg::Int(_)) => {
            diags.push(Diagnostic::type_error(
                span,
                "`Vec` second argument must be a unit, not an integer",
            ));
            return Ty::Error;
        }
    };
    Ty::Vec(n, dim)
}

/// Build a synthetic `Atom` `UnitExpr` for a single-atom unit that arrived
/// as `TypeArg::Type(Named("kg"))` because the parser couldn't disambiguate
/// it from a type at the lookahead boundary. Routes through `eval_unit_expr`
/// so unknown-unit diagnostics match the compound-form path.
fn synthesize_atom_unit_expr(t: &Type, name: &str) -> crate::ast::UnitExpr {
    crate::ast::UnitExpr {
        kind: crate::ast::UnitExprKind::Atom(name.to_string()),
        span: t.span,
        id: t.id,
    }
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
    subst: Option<&ParamSubst<'_>>,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match args {
        [TypeArg::Type(t)] => Ty::Array(Box::new(lower_type_inner(
            t,
            resolutions,
            definitions,
            subst,
            diags,
        ))),
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
    subst: Option<&ParamSubst<'_>>,
    diags: &mut Vec<Diagnostic>,
) -> Ty {
    match args {
        [TypeArg::Type(k), TypeArg::Type(v)] => Ty::Dict(
            Box::new(lower_type_inner(k, resolutions, definitions, subst, diags)),
            Box::new(lower_type_inner(v, resolutions, definitions, subst, diags)),
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
        let (resolutions, defs, _, _) = resolve_program(&prog);
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
    fn lower_scalar_with_kg_unit_produces_kg_dimension() {
        let (ty, diags) = lower_first_let_ty("let x: Scalar<kg> = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension([0, 1, 0, 0, 0, 0, 0])));
        assert!(
            diags.is_empty(),
            "expected clean lowering, got diags: {:?}",
            diags
        );
    }

    #[test]
    fn lower_scalar_with_compound_unit_meters_per_second() {
        let (ty, diags) = lower_first_let_ty("let v: Scalar<m/s> = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension([1, 0, -1, 0, 0, 0, 0])));
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn lower_scalar_with_derived_unit_newton() {
        let (ty, diags) = lower_first_let_ty("let f: Scalar<N> = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension([1, 1, -2, 0, 0, 0, 0])));
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn lower_scalar_with_unknown_unit_emits_diag() {
        let (ty, diags) = lower_first_let_ty("let x: Scalar<xyz> = 0.0");
        // Falls back to ZERO (cascade suppression).
        assert_eq!(ty, Ty::Scalar(Dimension::ZERO));
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unknown unit"));
        assert!(diags[0].message.contains("xyz"));
    }

    #[test]
    fn lower_scalar_dimensionless_no_args() {
        let (ty, diags) = lower_first_let_ty("let x: Scalar = 0.0");
        assert_eq!(ty, Ty::Scalar(Dimension::ZERO));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_vec_with_unit_kg() {
        let (ty, diags) = lower_first_let_ty("let v: Vec<3, kg> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension([0, 1, 0, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_vec_with_compound_unit_meters_per_second() {
        let (ty, diags) = lower_first_let_ty("let v: Vec<3, m/s> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension([1, 0, -1, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_vec_with_derived_unit_force() {
        let (ty, diags) = lower_first_let_ty("let f: Vec<3, N> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension([1, 1, -2, 0, 0, 0, 0])));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_vec_no_unit_is_dimensionless() {
        let (ty, diags) = lower_first_let_ty("let v: Vec<3> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension::ZERO));
        assert!(diags.is_empty());
    }

    #[test]
    fn lower_vec_with_unknown_unit_emits_diag() {
        let (ty, diags) = lower_first_let_ty("let v: Vec<3, xyz> = 0");
        assert_eq!(ty, Ty::Vec(3, Dimension::ZERO));
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unknown unit"));
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
        let (resolutions, defs, _, _) = resolve_program(&prog);
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
    fn ty_param_variant_compiles() {
        // Constructibility check: ensures the `Ty` enum exposes the new
        // `Param(usize)` schema sentinel. Variant signatures (Task 3) and
        // stdlib generics (PR-3e) populate `def_types` with shapes such as
        // `Function([Param(0)], Enum(option_def, [Param(0)]))`.
        let _t = Ty::Param(0);
        let _u = Ty::Function(
            vec![Ty::Param(0)],
            Box::new(Ty::Enum(DefId(0), vec![Ty::Param(0)])),
        );
    }

    #[test]
    fn lower_user_generic_enum_concrete_args() {
        // `Result<Int, String>` lowers to `Ty::Enum(result_def, [Int, String])`.
        let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nlet r: Result<Int, String> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[1];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        assert!(
            matches!(&ty, Ty::Enum(_, args) if args.len() == 2 && args[0] == Ty::Int && args[1] == Ty::String),
            "ty: {ty:?}"
        );
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn lower_user_generic_arity_too_few() {
        // `Result<Int>` is missing the second argument — diag must name the
        // expected count (2) so the user can correct the annotation.
        let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nlet r: Result<Int> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[1];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        assert_eq!(ty, Ty::Error);
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("expects 2 type argument"));
    }

    #[test]
    fn lower_user_generic_arity_too_many() {
        // `Maybe<Int, String>` against `enum Maybe<T>` — diag must name 1.
        let src = "enum Maybe<T>\n  Just(T)\n  Nothing\nend\nlet m: Maybe<Int, String> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[1];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        assert_eq!(ty, Ty::Error);
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(diags[0].message.contains("expects 1 type argument"));
    }

    #[test]
    fn lower_user_generic_nested() {
        // `Result<Maybe<Int>, String>` — nested generic must lower the inner
        // Maybe<Int> recursively before wrapping in the outer Result.
        let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nenum Maybe<T>\n  Just(T)\n  Nothing\nend\nlet x: Result<Maybe<Int>, String> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[2];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        assert!(diags.is_empty(), "diags: {:?}", diags);
        if let Ty::Enum(_, args) = ty {
            assert_eq!(args.len(), 2);
            assert!(
                matches!(&args[0], Ty::Enum(_, inner) if inner.len() == 1 && inner[0] == Ty::Int),
                "args[0]: {:?}",
                args[0]
            );
            assert_eq!(args[1], Ty::String);
        } else {
            panic!("expected outer Enum, got: {ty:?}");
        }
    }

    #[test]
    fn lower_non_enum_used_with_args_diag() {
        // `Point<Int>` against `struct Point` — Point isn't generic, must
        // emit "not a generic type" rather than silently lowering.
        let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point<Int> = 0";
        let prog = parse(tokenize(src).unwrap()).unwrap();
        let (resolutions, defs, _, _) = resolve_program(&prog);
        let mut diags = Vec::new();
        let item = &prog.items[1];
        let ty = match item {
            crate::ast::Item::Let(l) => lower_type(&l.ty, &resolutions, &defs, &mut diags),
            _ => panic!("expected Let item"),
        };
        assert_eq!(ty, Ty::Error);
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("not a generic type"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn dimension_mul_pointwise_adds_elements() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        let m_per_s = Dimension([1, 0, -1, 0, 0, 0, 0]);
        // kg * m/s = kg*m/s = [1, 1, -1, 0, 0, 0, 0]
        let result = kg.mul(m_per_s).unwrap();
        assert_eq!(result, Dimension([1, 1, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_mul_overflow_returns_err() {
        let big = Dimension([100, 0, 0, 0, 0, 0, 0]);
        let bigger = Dimension([50, 0, 0, 0, 0, 0, 0]);
        // 100 + 50 = 150, overflows i8 (max 127).
        assert_eq!(big.mul(bigger), Err(OverflowError));
    }

    #[test]
    fn dimension_div_pointwise_subtracts_elements() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        let s = Dimension([0, 0, 1, 0, 0, 0, 0]);
        // m / s = [1, 0, -1, 0, 0, 0, 0]
        let result = m.div(s).unwrap();
        assert_eq!(result, Dimension([1, 0, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_div_underflow_returns_err() {
        let small = Dimension([-100, 0, 0, 0, 0, 0, 0]);
        let big_pos = Dimension([50, 0, 0, 0, 0, 0, 0]);
        // -100 - 50 = -150, underflows i8 (min -128).
        assert_eq!(small.div(big_pos), Err(OverflowError));
    }

    #[test]
    fn dimension_pow_multiplies_elements_by_exponent() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        // m ^ 3 = m^3 = [3, 0, 0, 0, 0, 0, 0]
        let result = m.pow(3).unwrap();
        assert_eq!(result, Dimension([3, 0, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn dimension_pow_overflow_returns_err() {
        let m_strong = Dimension([10, 0, 0, 0, 0, 0, 0]);
        // 10 * 50 = 500, overflows i8.
        assert_eq!(m_strong.pow(50), Err(OverflowError));
    }

    #[test]
    fn dimension_pow_zero_yields_dimensionless() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(kg.pow(0).unwrap(), Dimension::ZERO);
    }

    #[test]
    fn dimension_pow_negative_works() {
        let s = Dimension([0, 0, 1, 0, 0, 0, 0]);
        // s ^ -2 = [0, 0, -2, 0, 0, 0, 0] (e.g. acceleration unit denominator)
        assert_eq!(s.pow(-2).unwrap(), Dimension([0, 0, -2, 0, 0, 0, 0]));
    }

    #[test]
    fn format_si_dimensionless_is_one() {
        assert_eq!(Dimension::ZERO.format_si(), "1");
    }

    #[test]
    fn format_si_single_base_unit_no_exponent() {
        let m = Dimension([1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(m.format_si(), "m");
    }

    #[test]
    fn format_si_kg_no_exponent() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(kg.format_si(), "kg");
    }

    #[test]
    fn format_si_negative_exponent() {
        let inv_s = Dimension([0, 0, -1, 0, 0, 0, 0]);
        assert_eq!(inv_s.format_si(), "s^-1");
    }

    #[test]
    fn format_si_multi_component_force_in_base_form() {
        // N = kg*m*s^-2 = [1, 1, -2, 0, 0, 0, 0]
        let newton_base = Dimension([1, 1, -2, 0, 0, 0, 0]);
        assert_eq!(newton_base.format_si(), "m*kg*s^-2");
    }

    #[test]
    fn format_si_higher_positive_exponent() {
        // m^3 (volume) = [3, 0, 0, 0, 0, 0, 0]
        let cubic_m = Dimension([3, 0, 0, 0, 0, 0, 0]);
        assert_eq!(cubic_m.format_si(), "m^3");
    }

    #[test]
    fn format_si_skips_zero_exponents() {
        // m^2 / s = [2, 0, -1, 0, 0, 0, 0] — kg, A, K, mol, cd zero exponents skipped.
        let acc_like = Dimension([2, 0, -1, 0, 0, 0, 0]);
        assert_eq!(acc_like.format_si(), "m^2*s^-1");
    }

    #[test]
    fn dimension_display_delegates_to_format_si() {
        let kg = Dimension([0, 1, 0, 0, 0, 0, 0]);
        assert_eq!(format!("{}", kg), "kg");
        assert_eq!(format!("{}", Dimension::ZERO), "1");
    }

    #[test]
    fn unit_registry_si_base_seven() {
        assert_eq!(
            UnitRegistry::lookup("m"),
            Some(Dimension([1, 0, 0, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("kg"),
            Some(Dimension([0, 1, 0, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("s"),
            Some(Dimension([0, 0, 1, 0, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("A"),
            Some(Dimension([0, 0, 0, 1, 0, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("K"),
            Some(Dimension([0, 0, 0, 0, 1, 0, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("mol"),
            Some(Dimension([0, 0, 0, 0, 0, 1, 0]))
        );
        assert_eq!(
            UnitRegistry::lookup("cd"),
            Some(Dimension([0, 0, 0, 0, 0, 0, 1]))
        );
    }

    #[test]
    fn unit_registry_derived_newton() {
        // N = kg*m/s^2 = [1, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("N"),
            Some(Dimension([1, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_joule() {
        // J = N*m = kg*m^2/s^2 = [2, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("J"),
            Some(Dimension([2, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_watt() {
        // W = J/s = kg*m^2/s^3 = [2, 1, -3, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("W"),
            Some(Dimension([2, 1, -3, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_pascal() {
        // Pa = N/m^2 = kg/(m*s^2) = [-1, 1, -2, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Pa"),
            Some(Dimension([-1, 1, -2, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_hertz() {
        // Hz = 1/s = [0, 0, -1, 0, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Hz"),
            Some(Dimension([0, 0, -1, 0, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_coulomb() {
        // C = A*s = [0, 0, 1, 1, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("C"),
            Some(Dimension([0, 0, 1, 1, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_volt() {
        // V = W/A = kg*m^2/(s^3*A) = [2, 1, -3, -1, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("V"),
            Some(Dimension([2, 1, -3, -1, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_derived_ohm() {
        // Ω = V/A = kg*m^2/(s^3*A^2) = [2, 1, -3, -2, 0, 0, 0]
        assert_eq!(
            UnitRegistry::lookup("Ω"),
            Some(Dimension([2, 1, -3, -2, 0, 0, 0]))
        );
    }

    #[test]
    fn unit_registry_unknown_returns_none() {
        assert_eq!(UnitRegistry::lookup("unknown_unit"), None);
        assert_eq!(UnitRegistry::lookup("km"), None); // SI prefix not in registry
        assert_eq!(UnitRegistry::lookup("cm"), None); // CGS not in registry
    }

    fn unit_atom(name: &str) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Atom(name.into()),
            span: crate::source::Span::new(0, name.len()),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_mul(a: crate::ast::UnitExpr, b: crate::ast::UnitExpr) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Mul(Box::new(a), Box::new(b)),
            span: crate::source::Span::new(0, 1),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_div(a: crate::ast::UnitExpr, b: crate::ast::UnitExpr) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Div(Box::new(a), Box::new(b)),
            span: crate::source::Span::new(0, 1),
            id: crate::ids::NodeId(0),
        }
    }

    fn unit_pow(base: crate::ast::UnitExpr, n: i64) -> crate::ast::UnitExpr {
        crate::ast::UnitExpr {
            kind: crate::ast::UnitExprKind::Pow(Box::new(base), n),
            span: crate::source::Span::new(0, 1),
            id: crate::ids::NodeId(0),
        }
    }

    #[test]
    fn eval_unit_expr_atom_kg() {
        let u = unit_atom("kg");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([0, 1, 0, 0, 0, 0, 0]));
        assert!(diags.is_empty());
    }

    #[test]
    fn eval_unit_expr_unknown_atom_emits_diag_returns_zero() {
        let u = unit_atom("xyz_unit");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension::ZERO);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("unknown unit"));
        assert!(diags[0].message.contains("xyz_unit"));
    }

    #[test]
    fn eval_unit_expr_mul_combines_dimensions() {
        // m * s → [1, 0, 1, 0, 0, 0, 0]
        let u = unit_mul(unit_atom("m"), unit_atom("s"));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([1, 0, 1, 0, 0, 0, 0]));
        assert!(diags.is_empty());
    }

    #[test]
    fn eval_unit_expr_div_subtracts_dimensions() {
        // m / s → [1, 0, -1, 0, 0, 0, 0]
        let u = unit_div(unit_atom("m"), unit_atom("s"));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([1, 0, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn eval_unit_expr_pow_multiplies_exponent() {
        // m^2 → [2, 0, 0, 0, 0, 0, 0]
        let u = unit_pow(unit_atom("m"), 2);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([2, 0, 0, 0, 0, 0, 0]));
    }

    #[test]
    fn eval_unit_expr_negative_exponent() {
        // s^-1 (frequency) → [0, 0, -1, 0, 0, 0, 0]
        let u = unit_pow(unit_atom("s"), -1);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([0, 0, -1, 0, 0, 0, 0]));
    }

    #[test]
    fn eval_unit_expr_compound_meters_per_second_squared() {
        // m / s^2 → [1, 0, -2, 0, 0, 0, 0] (acceleration)
        let u = unit_div(unit_atom("m"), unit_pow(unit_atom("s"), 2));
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([1, 0, -2, 0, 0, 0, 0]));
    }

    #[test]
    fn eval_unit_expr_overflow_emits_dimension_overflow_diag() {
        // m^100 → element 100, then ^2 = 200 overflows i8.
        let u = unit_pow(unit_pow(unit_atom("m"), 100), 2);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension::ZERO);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("dimension component overflow"));
    }

    #[test]
    fn eval_unit_expr_exponent_out_of_i8_range_diag() {
        // kg^1000 — exponent literal 1000 > i8::MAX = 127.
        let u = unit_pow(unit_atom("kg"), 1000);
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension::ZERO);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("out of valid range"));
        assert!(diags[0].message.contains("1000"));
    }

    #[test]
    fn eval_unit_expr_derived_unit_lookup_force() {
        // N → [1, 1, -2, 0, 0, 0, 0] (Newton)
        let u = unit_atom("N");
        let mut diags = Vec::new();
        let dim = eval_unit_expr(&u, &mut diags);
        assert_eq!(dim, Dimension([1, 1, -2, 0, 0, 0, 0]));
        assert!(diags.is_empty());
    }
}
