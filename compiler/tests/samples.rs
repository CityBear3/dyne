//! Compile every `.dy` file under `samples/` so that documentation samples
//! cannot bit-rot when the compiler changes.

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
        // Every documented sample must compile cleanly through ALL phases
        // (lex, parse, sema). PR-3d-α temporarily softened this to tolerate
        // Sema diagnostics: annotations carried real `Dimension` values, but
        // dim-carrying lets (e.g. `let m: Scalar<kg> = 1.0` in
        // harmonic_oscillator.dy) had no literal→unit coercion and so emitted
        // type-mismatch diags. PR-3d-β restores the full gate — the Q10
        // coercion (spec §4.7) + operator dimension propagation make those
        // samples compile clean again.
        if let Err(err) = dyne::compile(&source) {
            panic!("{path:?} failed to compile cleanly: {err:?}");
        }
        count += 1;
    }

    assert!(count > 0, "no .dy samples found in {dir:?}");
}

#[test]
fn units_force_sample_compiles_clean() {
    // F = m * a → Vec<3, N> (Scalar<kg> * Vec<3, m/s^2>, canonical Newton).
    let src = std::fs::read_to_string(samples_dir().join("units_force.dy")).expect("sample file");
    assert!(
        dyne::compile(&src).is_ok(),
        "units_force.dy should compile; diags: {:?}",
        dyne::compile(&src).err()
    );
}

#[test]
fn units_kinetic_energy_sample_compiles_clean() {
    // E_k = 0.5 * m * v^2 → Scalar<J> (kg * (m/s)^2, canonical Joule).
    let src = std::fs::read_to_string(samples_dir().join("units_kinetic_energy.dy"))
        .expect("sample file");
    assert!(
        dyne::compile(&src).is_ok(),
        "units_kinetic_energy.dy should compile; diags: {:?}",
        dyne::compile(&src).err()
    );
}
