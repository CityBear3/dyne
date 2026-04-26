//! Calculator compiler library.

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod source;

use crate::ast::Program;
use crate::error::CompileError;

pub fn compile(source: &str) -> Result<Program, CompileError> {
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
        assert_eq!(err.kind, crate::error::ErrorKind::Lex);
    }

    #[test]
    fn parse_error_propagates() {
        let err = compile("let").unwrap_err();
        assert_eq!(err.kind, crate::error::ErrorKind::Parse);
    }
}
