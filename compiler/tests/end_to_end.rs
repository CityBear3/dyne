//! End-to-end compilation smoke tests.

use calculator::{
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
