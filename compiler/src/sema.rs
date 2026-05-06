//! Semantic analysis (Stage 3): name resolution and type checking.
//!
//! PR-3a populates the resolution side of this module. PR-3b adds basic
//! type checking; later PRs add generics, units, and stdlib signatures.

pub mod diag;
pub mod resolve;
