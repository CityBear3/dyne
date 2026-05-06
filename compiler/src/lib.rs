//! Dyne compiler library.

pub mod ast;
pub mod diag;
pub mod source;

pub(crate) mod lexer;
pub(crate) mod parser;

use crate::ast::Program;
use crate::diag::Diagnostic;

pub fn compile(source: &str) -> Result<Program, Diagnostic> {
    let tokens = lexer::tokenize(source)?;
    parser::parse(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_empty_source_returns_empty_program() {
        let p = compile("").unwrap();
        assert_eq!(p.items.len(), 0);
    }

    #[test]
    fn compile_single_let() {
        let p = compile("let x: Scalar = 1.0").unwrap();
        assert_eq!(p.items.len(), 1);
    }

    #[test]
    fn compile_function() {
        let src = "function add(a: Scalar, b: Scalar): Scalar\n  return a + b\nend";
        let p = compile(src).unwrap();
        assert_eq!(p.items.len(), 1);
    }

    #[test]
    fn lex_error_propagates() {
        let err = compile("@").unwrap_err();
        assert_eq!(err.phase, crate::diag::Phase::Lex);
    }

    #[test]
    fn parse_error_propagates() {
        let err = compile("let").unwrap_err();
        assert_eq!(err.phase, crate::diag::Phase::Parse);
    }
}
