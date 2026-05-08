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
    // Use names that don't shadow the built-in `Result<T, E>` and its
    // variants `Ok`/`Err` (PR-3c Task 6 made them visible to all
    // programs). The test exercises generic enum declaration syntax, not
    // the specific names.
    let src = "enum MyResult<T, E>\n  MyOk(T)\n  MyErr(E)\nend";
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

// ----- PR-3c Task 6: built-in Option<T> and Result<T, E> -----

#[test]
fn builtin_option_resolves_in_type_annotation() {
    let result = dyne::compile("function f(): Option<Int>\n  return Some(1)\nend");
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn builtin_result_resolves_in_type_annotation() {
    let result = dyne::compile("function f(): Result<Int, String>\n  return Ok(42)\nend");
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn builtin_some_none_visible() {
    let result = dyne::compile(
        "function f(): Option<Int>\n  return None\nend\nfunction g(): Option<Int>\n  return Some(1)\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn builtin_ok_err_visible() {
    let result = dyne::compile(
        "function f(): Result<Int, String>\n  return Ok(1)\nend\nfunction g(): Result<Int, String>\n  return Err(\"x\")\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn builtin_match_option_compiles() {
    let result = dyne::compile(
        "function f(o: Option<Int>): Int\n  return match o\n    case Some(x) then x\n    case None then 0\n  end\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

// ----- PR-3c Task 8: end-to-end + carry regressions -----

#[test]
fn compile_generic_enum_with_exhaustive_match() {
    // Canonical generic-enum + match form using built-in Option<Int>.
    let result = dyne::compile(
        "function f(o: Option<Int>): Int\n  return match o\n    case Some(x) then x\n    case None then 0\n  end\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn compile_generic_match_non_exhaustive_yields_diagnostic() {
    // `Option<Int>` with only `Some` covered — Task 7 exhaustiveness
    // surfaces the missing `None` variant as a single diag.
    let result = dyne::compile(
        "function f(o: Option<Int>): Int\n  return match o\n    case Some(x) then x\n  end\nend",
    );
    let diags = result.unwrap_err();
    assert_eq!(diags.len(), 1, "diags: {:?}", diags);
    assert!(
        diags[0].message.contains("None"),
        "msg: {}",
        diags[0].message
    );
}

#[test]
fn compile_result_with_pattern_binding() {
    let result = dyne::compile(
        "function f(r: Result<Int, String>): Int\n  return match r\n    case Ok(v) then v\n    case Err(_) then -1\n  end\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn compile_user_defined_generic_enum_e2e() {
    // User-defined generic enum exercised end-to-end alongside the
    // built-ins — confirms the `compile()` pipeline doesn't hard-code
    // any specific enum names beyond the built-ins.
    let result = dyne::compile(
        "enum Maybe<T>\n  Just(T)\n  Nothing\nend\nfunction f(m: Maybe<Int>): Int\n  return match m\n    case Just(x) then x\n    case Nothing then 0\n  end\nend",
    );
    assert!(
        result.is_ok(),
        "expected clean compile, got: {:?}",
        result.err()
    );
}

#[test]
fn compile_pow_diag_uses_caret_syntax() {
    // Regression for the synth_pow text fix bundled in this task. The
    // previous diag text referenced `**` from an early prototype; the
    // language now consistently calls the operator `^`.
    let diags = dyne::compile("function f(): Int\n  return true ^ 2\nend").unwrap_err();
    assert!(
        diags.iter().any(|d| d.message.contains("`^`")),
        "expected `^` in diag, got: {:?}",
        diags
    );
    assert!(
        diags.iter().all(|d| !d.message.contains("`**`")),
        "no diag should reference `**`, got: {:?}",
        diags
    );
}

#[test]
fn match_inline_nested_generic_missing_inner_some_none_diag() {
    // PR-3c CQ #1 regression: when the scrutinee is constructed inline
    // (`Some(Some(1))`), the outer Option's type-arg is a still-unbound
    // unification var at the time `synth_match` runs. The inner column's
    // payload type — substituted from the variant schema — therefore
    // resolves to `Ty::Var(_)` and exhaust falls through to its sentinel
    // skip arm, silently accepting the missing inner `None` arm.
    //
    // Fix: `synth_match` must deep-resolve the scrutinee through the
    // unification table before handing it to `check_exhaustive`, so the
    // inner column carries `Option<Int>` rather than `Option<Var(α)>`.
    let src = "function f(): Int\n  return match Some(Some(1))\n    case Some(Some(x)) then x\n    case None then 0\n  end\nend";
    let diags = dyne::compile(src).unwrap_err();
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("non-exhaustive") && d.message.contains("None")),
        "expected non-exhaustive diag mentioning missing inner `None`, got: {:?}",
        diags
    );
}

#[test]
fn compile_user_redeclares_builtin_option_yields_diag() {
    // Negative interaction with built-ins: user declares an `enum
    // Option<T>` that collides with the built-in. Resolver fires
    // `duplicate_name` against the built-in's pre-existing entry.
    // Validates that built-ins are visible to the resolver's hoist
    // (otherwise no collision would surface) AND that the user gets a
    // meaningful diag rather than a silent override.
    let diags = dyne::compile("enum Option<T>\n  MyVariant(T)\nend").unwrap_err();
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("`Option`") && d.message.contains("already defined")),
        "expected duplicate-name diag for Option, got: {:?}",
        diags
    );
}
