//! Dyne compiler library.

pub mod ast;
pub mod diag;
pub mod ids;
pub mod sema;
pub mod source;

pub(crate) mod lexer;
pub(crate) mod parser;

pub use sema::{TypedProgram, check};

use crate::diag::Diagnostic;

pub fn compile(source: &str) -> Result<TypedProgram, Vec<Diagnostic>> {
    let tokens = lexer::tokenize(source).map_err(|d| vec![d])?;
    let program = parser::parse(tokens).map_err(|d| vec![d])?;
    sema::check(program)
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
