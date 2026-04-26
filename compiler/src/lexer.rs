//! Lexical analyzer.

pub(crate) mod scanner;
pub(crate) mod token;

pub(crate) use scanner::tokenize;
pub(crate) use token::{Token, TokenKind};
