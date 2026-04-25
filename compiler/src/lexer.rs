//! Lexical analyzer.

pub mod token;
pub mod scanner;

pub use scanner::tokenize;
pub use token::{Token, TokenKind};
