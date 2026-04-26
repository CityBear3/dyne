use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use dyne::{compile, source::SourceFile};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <source-file>", args[0]);
        return ExitCode::from(2);
    }
    let path = &args[1];
    if let Err(msg) = validate_extension(path) {
        eprintln!("error: {msg}");
        return ExitCode::from(2);
    }
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("failed to read {path}: {e}");
            return ExitCode::from(1);
        }
    };
    let source = SourceFile::new(text);
    match compile(source.text()) {
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

/// Reject source files that don't end in `.dy` (case-sensitive).
/// Returns a human-readable error message describing the mismatch.
fn validate_extension(path: &str) -> Result<(), String> {
    match Path::new(path).extension().and_then(|e| e.to_str()) {
        Some("dy") => Ok(()),
        Some(other) => Err(format!(
            "expected source file with .dy extension, got .{other} ({path})"
        )),
        None => Err(format!(
            "expected source file with .dy extension, got file with no extension ({path})"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_simple_dy() {
        assert!(validate_extension("foo.dy").is_ok());
    }

    #[test]
    fn accepts_path_with_dy() {
        assert!(validate_extension("path/to/foo.dy").is_ok());
    }

    #[test]
    fn accepts_multi_dot_filename_ending_in_dy() {
        assert!(validate_extension("simulation.test.dy").is_ok());
    }

    #[test]
    fn rejects_other_extension() {
        let err = validate_extension("foo.rs").unwrap_err();
        assert!(err.contains(".rs"));
    }

    #[test]
    fn rejects_missing_extension() {
        let err = validate_extension("foo").unwrap_err();
        assert!(err.contains("no extension"));
    }

    #[test]
    fn rejects_uppercase_dy() {
        // Case-sensitive — `.DY` is rejected to keep the convention strict.
        assert!(validate_extension("foo.DY").is_err());
    }

    #[test]
    fn rejects_dyne_extension() {
        // `.dyne` is not `.dy` — guards against typos.
        assert!(validate_extension("foo.dyne").is_err());
    }
}
