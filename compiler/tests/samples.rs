//! Parse every `.dy` file under `samples/` so that documentation samples
//! cannot bit-rot when the parser changes.

use std::path::PathBuf;

fn samples_dir() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.pop(); // drop "compiler"
    p.push("samples");
    p
}

/// Samples that exercise features not yet implemented in the current
/// compiler stage. They still parse, but `compile()` runs sema and rejects
/// them. Re-enable each entry as the corresponding PR lands.
const SAMPLES_AWAITING_LATER_PR: &[&str] = &[
    // Uses `Option<Measurement>` — user-defined generic enum instantiation
    // is deferred to PR-3c.
    "option_match.dy",
];

#[test]
fn every_sample_parses() {
    let dir = samples_dir();
    let entries = std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("cannot read {dir:?}: {e}"));

    let mut count = 0;
    for entry in entries {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("dy") {
            continue;
        }
        let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if SAMPLES_AWAITING_LATER_PR.contains(&file_name) {
            continue;
        }
        let source =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path:?}: {e}"));
        if let Err(err) = dyne::compile(&source) {
            panic!("{path:?} failed to parse: {err:?}");
        }
        count += 1;
    }

    assert!(count > 0, "no .dy samples found in {dir:?}");
}
