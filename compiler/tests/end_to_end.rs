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
    let p = compile(src).unwrap();
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
    let p = compile(src).unwrap();
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
    let p = compile(src).unwrap();
    assert_eq!(p.items.len(), 1);
}

#[test]
fn units_in_type_annotation() {
    let src = "let mass: Scalar<kg> = 1.5";
    let p = compile(src).unwrap();
    assert_eq!(p.items.len(), 1);
}

#[test]
fn stage2_struct_definition_compiles() {
    let src = "struct State\n  q: Vec<3>\n  p: Vec<3>\n  t: Scalar\nend";
    let prog = dyne::compile(src).unwrap();
    assert_eq!(prog.items.len(), 1);
}

#[test]
fn stage2_enum_with_generic_compiles() {
    let src = "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend";
    let prog = dyne::compile(src).unwrap();
    assert_eq!(prog.items.len(), 1);
}

#[test]
fn stage2_struct_literal_in_let_compiles() {
    let src =
        "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Point { x: 1.0, y: 2.0 }";
    let prog = dyne::compile(src).unwrap();
    assert_eq!(prog.items.len(), 2);
}

#[test]
fn stage2_match_with_literal_payload_compiles() {
    let src = "function classify(n: Option<Int>): Int\n  return match n\n    case Some(0) then 0\n    case Some(_) then 1\n    case None then -1\n  end\nend";
    let prog = dyne::compile(src).unwrap();
    assert_eq!(prog.items.len(), 1);
}

#[test]
fn stage2_float_pattern_rejected_e2e() {
    let src = "function f(x: Scalar): Int\n  return match x\n    case 0.5 then 1\n    case _ then 0\n  end\nend";
    let err = dyne::compile(src).unwrap_err();
    assert!(err.message.contains("floating-point"));
}
