//! Lexical analyzer.

pub(crate) mod token;
pub(crate) mod scanner;

pub(crate) use scanner::tokenize;
pub(crate) use token::{Token, TokenKind};
