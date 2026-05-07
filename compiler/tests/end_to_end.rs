//! End-to-end compilation smoke tests.

use dyne::{
    ast::{BinOp, ExprKind, Item, StmtKind},
    compile,
};

#[test]
fn harmonic_oscillator_like_snippet() {
    let src = "\
let k: Scalar = 0.5
let mass: Scalar = 1.0
function force(q: Vec<3>): Vec<3>
    return -k * q
end
";
    let p = compile(src).unwrap().program;
    assert_eq!(p.items.len(), 3);
    match &p.items[2] {
        Item::Function(f) => {
            assert_eq!(f.name, "force");
            assert_eq!(f.params.len(), 1);
            // body = return -k * q
            let stmt = &f.body.stmts[0];
            match &stmt.kind {
                StmtKind::Return(Some(e)) => match &e.kind {
                    ExprKind::BinOp(BinOp::Mul, _, _) => {}
                    other => panic!("unexpected return expr: {other:?}"),
                },
                _ => panic!("expected return stmt"),
            }
        }
        _ => panic!("expected Function"),
    }
}

#[test]
fn nested_if_compiles() {
    let src = "\
function sign(x: Scalar): Int
    if x > 0.0 then
        return 1
    elseif x == 0.0 then
        return 0
    else
        return -1
    end
end
";
    let p = compile(src).unwrap().program;
    assert_eq!(p.items.len(), 1);
}

#[test]
fn for_range_loop_in_function() {
    let src = "\
function sum(n: Int): Int
    let total: Int = 0
    for i = 0, n do
        total = total + i
    end
    return total
end
";
    let p = compile(src).unwrap().program;
    assert_eq!(p.items.len(), 1);
}

#[test]
fn units_in_type_annotation() {
    let src = "let mass: Scalar<kg> = 1.5";
    let p = compile(src).unwrap().program;
    assert_eq!(p.items.len(), 1);
}

#[test]
fn stage2_struct_definition_compiles() {
    let src = "struct State\n  q: Vec<3>\n  p: Vec<3>\n  t: Scalar\nend";
    let prog = dyne::compile(src).unwrap().program;
    assert_eq!(prog.items.len(), 1);
}

#[test]
fn stage2_enum_with_generic_compiles() {
    let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend";
    let prog = dyne::compile(src).unwrap().program;
    assert_eq!(prog.items.len(), 1);
}

#[test]
fn stage2_struct_literal_in_let_compiles() {
    let src =
        "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Point { x: 1.0, y: 2.0 }";
    let prog = dyne::compile(src).unwrap().program;
    assert_eq!(prog.items.len(), 2);
}

#[test]
fn stage2_match_with_literal_payload_compiles() {
    // Adapted from a previous version that referenced the built-in
    // `Option<Int>`. Built-in enums (Option, Result) land in PR-3c; until
    // then this test uses a user-defined enum to exercise the same
    // match-with-literal-pattern code paths.
    let src = "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction classify(n: Maybe): Int\n  return match n\n    case Just(0) then 0\n    case Just(_) then 1\n    case Nothing then -1\n  end\nend";
    let prog = dyne::compile(src).unwrap().program;
    assert_eq!(prog.items.len(), 2);
}

#[test]
fn stage2_float_pattern_rejected_e2e() {
    let src = "function f(x: Scalar): Int\n  return match x\n    case 0.5 then 1\n    case _ then 0\n  end\nend";
    let err = dyne::compile(src).unwrap_err();
    assert!(err[0].message.contains("floating-point"));
}

#[test]
fn compile_undefined_name_yields_sema_diagnostic() {
    let src = "function f(): Int\n  return undefined_var\nend";
    let diags = dyne::compile(src).unwrap_err();
    // One undefined reference → exactly one diagnostic.
    assert_eq!(diags.len(), 1, "got {:?}", diags);
    assert_eq!(diags[0].phase, dyne::diag::Phase::Sema);
    assert_eq!(diags[0].level, dyne::diag::Level::Error);
    assert!(diags[0].message.contains("undefined_var"));
}

#[test]
fn compile_multiple_undefined_names_emits_multiple_diagnostics() {
    let src = "function f(): Int\n  return a + b\nend";
    let diags = dyne::compile(src).unwrap_err();
    // Two undefined references → exactly two diagnostics, one per name.
    assert_eq!(diags.len(), 2, "got {:?}", diags);
    assert!(diags[0].message.contains("`a`"));
    assert!(diags[1].message.contains("`b`"));
}

#[test]
fn compile_duplicate_top_level_definition_yields_diagnostic() {
    let src = "let x: Int = 1\nlet x: Int = 2";
    let diags = dyne::compile(src).unwrap_err();
    // Single duplicate → exactly one diagnostic.
    assert_eq!(diags.len(), 1, "got {:?}", diags);
    assert_eq!(diags[0].phase, dyne::diag::Phase::Sema);
    assert!(diags[0].message.contains("`x`"));
}

// ----- PR-3b Task 7: end-to-end type-checking surface -----
//
// These tests pin compile()'s public-API behavior under the Pass 2
// type checker. Per-task tests in `compiler/src/sema/check.rs` already
// exercise individual rules; the e2e tests here verify the full
// lex → parse → resolve → signature-pass → check pipeline emits the
// same diagnostics through `dyne::compile`.

#[test]
fn compile_int_to_int_function_succeeds() {
    let src = "function f(x: Int): Int\n  return x + 1\nend";
    let typed = dyne::compile(src).unwrap();
    assert_eq!(typed.program.items.len(), 1);
}

#[test]
fn compile_type_mismatch_in_return_yields_diagnostic() {
    let src = "function f(): Int\n  return true\nend";
    let diags = dyne::compile(src).unwrap_err();
    assert_eq!(diags.len(), 1, "got {:?}", diags);
    assert_eq!(diags[0].phase, dyne::diag::Phase::Sema);
    assert!(
        diags[0].message.contains("type mismatch"),
        "msg: {}",
        diags[0].message
    );
}

#[test]
fn compile_wrong_arity_function_call_yields_diagnostic() {
    let src = "function add(a: Int, b: Int): Int\n  return a + b\nend\nfunction f(): Int\n  return add(1)\nend";
    let diags = dyne::compile(src).unwrap_err();
    assert_eq!(diags.len(), 1, "got {:?}", diags);
    assert!(
        diags[0].message.contains("arguments"),
        "msg: {}",
        diags[0].message
    );
}

#[test]
fn compile_struct_field_access_succeeds() {
    let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nfunction get_x(p: Point): Scalar\n  return p.x\nend";
    let typed = dyne::compile(src).unwrap();
    assert_eq!(typed.program.items.len(), 2);
}

#[test]
fn compile_unknown_struct_field_yields_diagnostic() {
    let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nfunction get_z(p: Point): Scalar\n  return p.z\nend";
    let diags = dyne::compile(src).unwrap_err();
    assert_eq!(diags.len(), 1, "got {:?}", diags);
    assert!(
        diags[0].message.contains("`z`"),
        "msg: {}",
        diags[0].message
    );
}
