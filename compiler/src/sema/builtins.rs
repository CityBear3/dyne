//! Built-in type registration via `compiler/builtins/builtins.dy`.
//!
//! Per /design-discussion 2026-05-08 (Q4 / Path 2), the dyne compiler
//! embeds its built-in generic enums (`Option<T>`, `Result<T, E>`) as
//! a small dyne source file rather than synthesizing AST/Ty nodes
//! directly. The same lexer/parser/resolver/type-checker handles both
//! built-in and user code, which keeps the boundary minimal and the
//! self-host story clean.
//!
//! ## Pipeline
//!
//! `load_builtins(node_offset)` tokenizes and parses `builtins.dy`,
//! starting `NodeId` allocation at `node_offset` so the user source
//! (parsed afterwards with offset = built-ins' high-water-mark) gets a
//! disjoint id range. The function returns the parsed `Program` plus
//! the highest `NodeId` allocated, which `compile()` then uses as the
//! offset for user-source parsing.
//!
//! `compile()` merges the built-in `Program.items` with the user
//! `Program.items` into a single combined program before handing off
//! to `sema::check`. Subsequent phases (hoisting, signature_pass,
//! type-check) treat them uniformly — `Option`/`Result`/`Some`/`None`/
//! `Ok`/`Err` are visible to user code through the resolver's normal
//! top-level hoisting.
//!
//! ## Failure mode
//!
//! Any error processing `builtins.dy` is a compile-time bug in the
//! dyne compiler itself (the source is checked into the repo and
//! shouldn't depend on user input). `load_builtins` therefore panics
//! rather than surfacing diagnostics to user code.

use crate::ast::Program;
use crate::lexer::tokenize;
use crate::parser::parse_with_node_offset;

const BUILTINS_SOURCE: &str = include_str!("../../builtins/builtins.dy");

/// Output of `load_builtins`. Carries the parsed program and the next
/// NodeId after the built-ins so the user-source parser can continue
/// from a non-overlapping id range.
pub(crate) struct BuiltinsContext {
    pub(crate) program: Program,
    pub(crate) next_node_id: u32,
}

/// Tokenize + parse `builtins.dy`. Panics on any failure — built-ins
/// errors are compile-time bugs and never surface to user code.
pub(crate) fn load_builtins() -> BuiltinsContext {
    let tokens =
        tokenize(BUILTINS_SOURCE).unwrap_or_else(|e| panic!("built-ins lex failed: {e:?}"));
    let (program, next_node_id) = parse_with_node_offset(tokens, 0)
        .unwrap_or_else(|e| panic!("built-ins parse failed: {e:?}"));
    BuiltinsContext {
        program,
        next_node_id,
    }
}
