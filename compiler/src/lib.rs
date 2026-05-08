//! Dyne compiler library.

pub mod ast;
pub mod diag;
pub mod ids;
pub mod sema;
pub mod source;

pub(crate) mod lexer;
pub(crate) mod parser;

pub use sema::{TypedProgram, check};

use crate::ast::Program;
use crate::diag::Diagnostic;

/// Compile a dyne source string.
///
/// Built-in generic enums (`Option<T>`, `Result<T, E>`) are loaded from
/// `compiler/builtins/builtins.dy` (embedded via `include_str!`) and
/// merged into the user program before semantic analysis. The resolver's
/// top-level hoist then makes them visible to user code through the same
/// path as user-declared enums — there is no `#[builtin]` annotation or
/// special-cased name list. Built-ins compile failure is a compile-time
/// bug and panics; user diagnostics carry the user-source span (the
/// built-ins occupy NodeIds 0..N and span positions in `builtins.dy`,
/// disjoint from user-source NodeIds and spans).
///
/// **Id-ordering invariant**: built-ins are parsed first (NodeIds
/// 0..N) and resolved before user code. Their DefIds are therefore
/// allocated first by the resolver — `Option`'s DefId is always
/// strictly less than any user-defined enum's DefId in the same
/// program. Downstream passes that compare DefIds for ordering must
/// not assume user definitions come first.
pub fn compile(source: &str) -> Result<TypedProgram, Vec<Diagnostic>> {
    // Phase 1: built-ins (panics on failure).
    let builtins_ctx = sema::builtins::load_builtins();
    let n_builtin_items = builtins_ctx.program.items.len();

    // Defensive built-ins-clean invariant. `sema::check` over the
    // built-ins-only Program must succeed with zero diagnostics —
    // anything else means a regression in `compiler/builtins/builtins.dy`
    // (or in a sema rule that fires against built-in items). We isolate
    // this from the user-source check because Span carries no source-
    // file identifier; trying to attribute a post-merge diagnostic back
    // to "user vs built-in" by byte range is heuristic at best.
    // Running sema::check over the built-ins alone removes that
    // ambiguity at the cost of one extra check_pass per compile —
    // `debug_assert!` confines that cost to debug builds, which is
    // where regressions are caught (CI runs in debug; release builds
    // ship a verified compiler).
    debug_assert!(
        sema::check(builtins_ctx.program.clone()).is_ok(),
        "compiler bug: builtins.dy must compile cleanly without sema \
         diagnostics — this indicates a regression in \
         compiler/builtins/builtins.dy (or in a sema rule that fires \
         against built-in items)"
    );

    // Phase 2: tokenize + parse user source with a NodeId offset so its
    // ids are disjoint from the built-ins'.
    let user_tokens = lexer::tokenize(source).map_err(|d| vec![d])?;
    let (user_program, _next_id) =
        parser::parse_with_node_offset(user_tokens, builtins_ctx.next_node_id)
            .map_err(|d| vec![d])?;
    // Phase 3: merge into a single Program. The resolver hoists all
    // top-level items (functions, structs, enums, variants), so built-in
    // types are visible to user code through the existing path.
    let combined = merge_programs(builtins_ctx.program, user_program);
    let mut typed = sema::check(combined)?;
    // Phase 4: strip built-in items from the user-visible Program so
    // tests / downstream consumers see only what the user wrote. Type
    // tables (definitions, def_types, variant_payloads, resolutions,
    // binding_def_ids) keep their built-in entries — those are needed
    // for use-site resolution / instantiation / pattern substitution.
    typed.program.items.drain(0..n_builtin_items);
    Ok(typed)
}

fn merge_programs(builtins: Program, user: Program) -> Program {
    let mut items = builtins.items;
    items.extend(user.items);
    // The combined program reuses the user program's outer span/id —
    // the built-in items live earlier in the items list but the
    // wrapping Program node is the user's. Spans on built-in items
    // point into `builtins.dy`; spans on user items point into user
    // source. Diagnostics naturally surface in the right source
    // because every Diagnostic carries its own item-level Span.
    Program {
        items,
        span: user.span,
        id: user.id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_empty_source_returns_empty_program() {
        let p = compile("").unwrap().program;
        assert_eq!(p.items.len(), 0);
    }

    #[test]
    fn compile_single_let() {
        let p = compile("let x: Scalar = 1.0").unwrap().program;
        assert_eq!(p.items.len(), 1);
    }

    #[test]
    fn compile_function() {
        let src = "function add(a: Scalar, b: Scalar): Scalar\n  return a + b\nend";
        let p = compile(src).unwrap().program;
        assert_eq!(p.items.len(), 1);
    }

    #[test]
    fn lex_error_propagates() {
        let err = compile("@").unwrap_err();
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].phase, crate::diag::Phase::Lex);
    }

    #[test]
    fn parse_error_propagates() {
        let err = compile("let").unwrap_err();
        assert_eq!(err.len(), 1);
        assert_eq!(err[0].phase, crate::diag::Phase::Parse);
    }
}
