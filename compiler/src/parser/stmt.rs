//! Statement and top-level item parser.

use crate::ast::Program;
use crate::error::CompileError;
use crate::parser::Parser;
use crate::source::Span;

pub fn parse_program(parser: &mut Parser) -> Result<Program, CompileError> {
    parser.consume_newlines();
    // TODO: parse items. Placeholder returns empty program.
    Ok(Program {
        items: vec![],
        span: Span::new(0, 0),
    })
}
