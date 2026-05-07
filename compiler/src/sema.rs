//! Semantic analysis (Stage 3): name resolution and type checking.
//!
//! PR-3a populates the resolution side of this module. PR-3b adds basic
//! type checking; later PRs add generics, units, and stdlib signatures.

pub mod diag;
pub mod resolve;

use std::collections::HashMap;

use crate::ast::Program;
use crate::diag::Diagnostic;
use crate::ids::NodeId;
use crate::sema::resolve::{DefinitionTable, ResolveTable};

/// Placeholder for PR-3b's TypeTable. PR-3a leaves it empty.
pub type TypeTable = HashMap<NodeId, ()>;

/// The output of `check()`. Aggregates the parsed program with all
/// annotation tables produced by sema phases.
///
/// `TypedProgram` is constructed only by `sema::check`; the private
/// constructor enforces the phase boundary at compile time. Stage 4
/// will accept `&TypedProgram` rather than `Program`.
#[derive(Debug)]
#[non_exhaustive]
pub struct TypedProgram {
    pub program: Program,
    pub types: TypeTable,
    pub resolutions: ResolveTable,
    pub definitions: DefinitionTable,
}

impl TypedProgram {
    fn new(
        program: Program,
        types: TypeTable,
        resolutions: ResolveTable,
        definitions: DefinitionTable,
    ) -> Self {
        Self {
            program,
            types,
            resolutions,
            definitions,
        }
    }
}

/// Run the semantic-analysis phases over a parsed program.
///
/// PR-3a only runs name resolution. Future PRs add type checking, generic
/// instantiation, unit checking, and precision-warning analysis.
pub fn check(program: Program) -> Result<TypedProgram, Vec<Diagnostic>> {
    let (resolutions, definitions, diags) = resolve::resolve_program(&program);
    if !diags.is_empty() {
        return Err(diags);
    }
    Ok(TypedProgram::new(
        program,
        TypeTable::new(),
        resolutions,
        definitions,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Program;
    use crate::lexer::tokenize;
    use crate::parser::parse;

    fn parse_src(src: &str) -> Program {
        parse(tokenize(src).unwrap()).unwrap()
    }

    #[test]
    fn check_valid_program_returns_typed_program() {
        let prog = parse_src("let x: Int = 1");
        let typed = check(prog).expect("expected ok");
        assert_eq!(typed.program.items.len(), 1);
        assert!(typed.types.is_empty(), "PR-3a leaves types table empty");
        assert_eq!(
            typed.definitions.len(),
            1,
            "the top-level let is the only def"
        );
    }

    #[test]
    fn check_program_with_undefined_name_returns_err() {
        let prog = parse_src("function f(): Int\n  return undefined_var\nend");
        let diags = check(prog).expect_err("expected sema error");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].phase, crate::diag::Phase::Sema);
        assert!(diags[0].message.contains("undefined_var"));
    }

    #[test]
    fn check_program_with_multiple_undefined_names_returns_all() {
        let prog = parse_src("function f(): Int\n  let x: Int = a + b\n  return c\nend");
        let diags = check(prog).expect_err("expected sema errors");
        // Three undefined names → exactly three diagnostics; pin the names
        // and order so a regression that emits a single name twice (or
        // skips one) fails loudly.
        assert_eq!(
            diags.len(),
            3,
            "expected exactly 3 diagnostics for a/b/c, got {:?}",
            diags
        );
        assert!(diags[0].message.contains("`a`"));
        assert!(diags[1].message.contains("`b`"));
        assert!(diags[2].message.contains("`c`"));
    }

    #[test]
    fn check_typed_program_resolutions_keyed_by_node_id() {
        let prog = parse_src("let k: Scalar = 0.5\nfunction f(): Scalar\n  return k\nend");
        let typed = check(prog).expect("expected ok");
        // The Ident("k") inside f's body has its own NodeId; that NodeId
        // must appear in the resolutions table.
        assert!(!typed.resolutions.is_empty());
        // And every value in the table maps to a DefId that exists in
        // definitions.
        for def_id in typed.resolutions.values() {
            assert!(typed.definitions.contains_key(def_id));
        }
    }
}
