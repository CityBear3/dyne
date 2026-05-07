//! Type representation for the sema phase.
//!
//! Populated incrementally through Stage 3:
//! - PR-3b: `Ty` enum, `Dimension` stub (ZERO only), `TypeVarId`, `lower_type`
//! - PR-3d: `Dimension` arithmetic (mul, div, pow), unit propagation through operators
//! - PR-3c: enum type-argument instantiation via `TypeVarId`

#![allow(dead_code)] // Consumers land in Tasks 2-6.

use crate::ids::DefId;

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
