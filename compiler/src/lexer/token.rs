//! Token types produced by the lexer.

use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TokenKind {
    // Literals
    Int(i64),
    Float(f64),
    Str(String),
    Ident(String),

    // Keywords
    Let,
    Function,
    End,
    Return,
    If,
    Then,
    Elseif,
    Else,
    For,
    In,
    Do,
    While,
    Match,
    Struct,
    Enum,
    Import,
    And,
    Or,
    Not,
    True,
    False,

    // Operators and punctuation
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Eq,
    EqEq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
    Colon,
    Comma,
    Dot,
    Arrow,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    // Structural
    Newline,
    Eof,
}

impl TokenKind {
    pub(crate) fn keyword(ident: &str) -> Option<TokenKind> {
        Some(match ident {
            "let" => TokenKind::Let,
            "function" => TokenKind::Function,
            "end" => TokenKind::End,
            "return" => TokenKind::Return,
            "if" => TokenKind::If,
            "then" => TokenKind::Then,
            "elseif" => TokenKind::Elseif,
            "else" => TokenKind::Else,
            "for" => TokenKind::For,
            "in" => TokenKind::In,
            "do" => TokenKind::Do,
            "while" => TokenKind::While,
            "match" => TokenKind::Match,
            "struct" => TokenKind::Struct,
            "enum" => TokenKind::Enum,
            "import" => TokenKind::Import,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "not" => TokenKind::Not,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keyword_lookup() {
        assert_eq!(TokenKind::keyword("let"), Some(TokenKind::Let));
        assert_eq!(TokenKind::keyword("function"), Some(TokenKind::Function));
        assert_eq!(TokenKind::keyword("foo"), None);
    }

    #[test]
    fn token_construction() {
        let t = Token {
            kind: TokenKind::Int(42),
            span: Span::new(0, 2),
        };
        assert_eq!(t.kind, TokenKind::Int(42));
    }
}
