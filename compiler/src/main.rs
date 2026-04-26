use std::env;
use std::fs;
use std::process::ExitCode;

use calculator::{compile, source::SourceFile};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <source-file>", args[0]);
        return ExitCode::from(2);
    }
    let path = &args[1];
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("failed to read {path}: {e}");
            return ExitCode::from(1);
        }
    };
    let source = SourceFile::new(text.clone());
    match compile(&text) {
        Ok(program) => {
            println!("parsed {} item(s)", program.items.len());
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("{}", err.render(&source));
            ExitCode::from(1)
        }
    }
}
