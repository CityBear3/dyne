//! Type expression parser.

use crate::ast::Type;
use crate::error::CompileError;
use crate::parser::Parser;

#[allow(dead_code)]
pub(crate) fn parse_type(_parser: &mut Parser) -> Result<Type, CompileError> {
    unimplemented!("parse_type will be implemented in Task 15")
}
