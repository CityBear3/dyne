//! Calculator compiler library.

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod source;

pub fn compile(_source: &str) -> Result<(), ()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_empty_source_ok() {
        assert_eq!(compile(""), Ok(()));
    }
}
