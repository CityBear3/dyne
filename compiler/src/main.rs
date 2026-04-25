fn main() {
    println!("Hello, world!");
}

struct Lexer {
    user_input: String,
}

impl Lexer {
    fn new(input: String) -> Self {
        Lexer { user_input: input }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn init_lexer() {
        let input = String::from("let x = 5;");
        let lexer = Lexer::new(input);
        assert_eq!(lexer.user_input, "let x = 5;");
    }
}
