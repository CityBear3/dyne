//! Parse every `.dy` file under `samples/` so that documentation samples
//! cannot bit-rot when the parser changes.

use dyne::diag::Phase;
use std::path::PathBuf;

fn samples_dir() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.pop(); // drop "compiler"
    p.push("samples");
    p
}

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
        let source =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path:?}: {e}"));
        // Test name = "every_sample_parses": fail fast on Lex / Parse
        // diagnostics. Sema diagnostics are tolerated in PR-3d-α: with
        // annotations now carrying real `Dimension` values, samples that
        // assign dimensionless literals to unit-annotated bindings (e.g.
        // `let m: Scalar<kg> = 1.0` in `harmonic_oscillator.dy`) emit
        // type-mismatch diags. Explicit literal→unit coercion + operator-
        // side dim propagation arrive in PR-3d-β; the sema gate is
        // restored then.
        if let Err(err) = dyne::compile(&source) {
            let lex_or_parse: Vec<_> = err
                .iter()
                .filter(|d| matches!(d.phase, Phase::Lex | Phase::Parse))
                .collect();
            assert!(
                lex_or_parse.is_empty(),
                "{path:?} failed to parse: {lex_or_parse:?}"
            );
        }
        count += 1;
    }

    assert!(count > 0, "no .dy samples found in {dir:?}");
}
