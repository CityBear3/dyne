//! Spec §6.1 precision-warning analysis (PR-3e).
//!
//! Post-check walker over the typed program: inside `for`/`while` bodies
//! (any nesting depth), an assignment `acc = acc + x` (or the commutative
//! `acc = x + acc`) where the target is a `Scalar` binding (any unit) and
//! `x` is any `Scalar`-typed expression risks rounding-error growth and
//! gets a `Level::Warning`. Conservative by design (DD "Precision warning
//! detection"): no attempt to prove the sum unsafe; false positives are
//! acceptable. `Int` accumulation is exact and excluded; subtraction and
//! cross-function flows are excluded; there is no suppression mechanism.

use std::collections::HashMap;

use crate::ast::{BinOp, Block, Expr, ExprKind, ForStmt, Item, Program, Stmt, StmtKind};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{DefinitionTable, ResolveTable};
use crate::sema::ty::Ty;

pub(crate) fn analyze(
    program: &Program,
    types: &HashMap<NodeId, Ty>,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    def_types: &HashMap<DefId, Ty>,
) -> Vec<Diagnostic> {
    let mut walker = Walker {
        types,
        resolutions,
        definitions,
        def_types,
        out: Vec::new(),
    };
    for item in &program.items {
        match item {
            Item::Function(f) => walker.walk_block(&f.body, false),
            Item::Let(l) => walker.walk_expr(&l.init, false),
            Item::Struct(_) | Item::Enum(_) | Item::Import(_) => {}
        }
    }
    walker.out
}

struct Walker<'a> {
    types: &'a HashMap<NodeId, Ty>,
    resolutions: &'a ResolveTable,
    definitions: &'a DefinitionTable,
    def_types: &'a HashMap<DefId, Ty>,
    out: Vec<Diagnostic>,
}

impl Walker<'_> {
    fn walk_block(&mut self, b: &Block, in_loop: bool) {
        for stmt in &b.stmts {
            self.walk_stmt(stmt, in_loop);
        }
    }

    fn walk_stmt(&mut self, s: &Stmt, in_loop: bool) {
        match &s.kind {
            StmtKind::Let(l) => self.walk_expr(&l.init, in_loop),
            StmtKind::Assign(_, value) => {
                if in_loop {
                    self.check_accumulation(s, value);
                }
                self.walk_expr(value, in_loop);
            }
            StmtKind::Expr(e) | StmtKind::Return(Some(e)) => self.walk_expr(e, in_loop),
            StmtKind::Return(None) => {}
            StmtKind::For(f) => match f {
                ForStmt::Range {
                    start, end, body, ..
                } => {
                    self.walk_expr(start, in_loop);
                    self.walk_expr(end, in_loop);
                    self.walk_block(body, true);
                }
                ForStmt::Iter { iter, body, .. } | ForStmt::IterKV { iter, body, .. } => {
                    self.walk_expr(iter, in_loop);
                    self.walk_block(body, true);
                }
            },
            StmtKind::While(w) => {
                self.walk_expr(&w.cond, in_loop);
                self.walk_block(&w.body, true);
            }
        }
    }

    /// Expressions can nest blocks (if / match / block-expr), and those
    /// blocks can contain further assignments — keep the loop flag flowing.
    fn walk_expr(&mut self, e: &Expr, in_loop: bool) {
        match &e.kind {
            ExprKind::If(i) => {
                self.walk_expr(&i.cond, in_loop);
                self.walk_block(&i.then_block, in_loop);
                for (cond, block) in &i.elseifs {
                    self.walk_expr(cond, in_loop);
                    self.walk_block(block, in_loop);
                }
                if let Some(b) = &i.else_block {
                    self.walk_block(b, in_loop);
                }
            }
            ExprKind::Match(scrut, arms) => {
                self.walk_expr(scrut, in_loop);
                for arm in arms {
                    self.walk_block(&arm.body, in_loop);
                }
            }
            ExprKind::Block(b) => self.walk_block(b, in_loop),
            ExprKind::BinOp(_, l, r) => {
                self.walk_expr(l, in_loop);
                self.walk_expr(r, in_loop);
            }
            ExprKind::UnaryOp(_, x) => self.walk_expr(x, in_loop),
            ExprKind::Call(callee, args) => {
                self.walk_expr(callee, in_loop);
                for a in args {
                    self.walk_expr(a, in_loop);
                }
            }
            ExprKind::Index(base, idx) => {
                self.walk_expr(base, in_loop);
                self.walk_expr(idx, in_loop);
            }
            ExprKind::FieldAccess(base, _) => self.walk_expr(base, in_loop),
            ExprKind::VecLit(elems) => {
                for x in elems {
                    self.walk_expr(x, in_loop);
                }
            }
            ExprKind::MatLit(rows) => {
                for row in rows {
                    for x in row {
                        self.walk_expr(x, in_loop);
                    }
                }
            }
            ExprKind::StructLit(_, fields) => {
                for (_, x) in fields {
                    self.walk_expr(x, in_loop);
                }
            }
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Ident(_)
            | ExprKind::Lambda(_) => {}
        }
    }

    /// `s` is an Assign statement inside a loop. Warn iff the target
    /// resolves to a `Scalar` binding and the RHS is `acc + x` / `x + acc`
    /// with a `Scalar`-typed `x`. The Assign target's DefId is keyed by the
    /// statement's own NodeId (mirrors `synth_stmt`'s Assign handling).
    fn check_accumulation(&mut self, s: &Stmt, value: &Expr) {
        let Some(acc_def) = self.resolutions.get(&s.id).copied() else {
            return;
        };
        if !matches!(self.def_types.get(&acc_def), Some(Ty::Scalar(_))) {
            return;
        }
        let ExprKind::BinOp(BinOp::Add, l, r) = &value.kind else {
            return;
        };
        let addend = if self.is_use_of(l, acc_def) {
            r
        } else if self.is_use_of(r, acc_def) {
            l
        } else {
            return;
        };
        if !matches!(self.types.get(&addend.id), Some(Ty::Scalar(_))) {
            return;
        }
        let binding_span = self.definitions.get(&acc_def).map(|d| d.span);
        self.out.push(crate::sema::diag::precision_accumulation(
            value.span,
            binding_span,
        ));
    }

    fn is_use_of(&self, e: &Expr, def: DefId) -> bool {
        matches!(&e.kind, ExprKind::Ident(_)) && self.resolutions.get(&e.id) == Some(&def)
    }
}

#[cfg(test)]
mod tests {
    use crate::diag::{Diagnostic, Level};

    fn warnings_for(src: &str) -> Vec<Diagnostic> {
        let prog = crate::parser::parse(crate::lexer::tokenize(src).unwrap()).unwrap();
        crate::sema::check(prog)
            .expect("expected successful check")
            .warnings
    }

    #[test]
    fn canonical_accumulation_in_for_warns() {
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total + 1.5\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
        assert_eq!(w[0].level, Level::Warning);
    }

    #[test]
    fn commutative_accumulation_warns() {
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = 1.5 + total\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn accumulation_in_while_warns() {
        // Mirror the while-loop surface syntax used by the parser's own
        // while tests (parser/stmt.rs) if this literal differs.
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  while total < 10.0 do\n    total = total + 1.5\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn computed_scalar_addend_warns() {
        let w = warnings_for(
            "function s(a: Scalar, b: Scalar): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total + a * b\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn unit_carrying_accumulator_warns() {
        let w = warnings_for(
            "function s(x: Scalar<m>): Scalar<m>\n  let total: Scalar<m> = 0.0\n  for i = 0, 3 do\n    total = total + x\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn accumulation_nested_in_if_inside_loop_warns() {
        let w = warnings_for(
            "function s(c: Bool): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    if c then\n      total = total + 1.5\n    end\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn int_accumulator_is_exact_no_warning() {
        let w = warnings_for(
            "function s(): Int\n  let total: Int = 0\n  for i = 0, 3 do\n    total = total + i\n  end\n  return total\nend",
        );
        assert!(w.is_empty(), "warnings: {w:?}");
    }

    #[test]
    fn int_addend_no_warning() {
        // `total + 1`: the addend's recorded type is Int (promotion happens
        // in the checker, not in the recorded operand type) — excluded.
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total + 1\n  end\n  return total\nend",
        );
        assert!(w.is_empty(), "warnings: {w:?}");
    }

    #[test]
    fn subtraction_no_warning() {
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total - 1.5\n  end\n  return total\nend",
        );
        assert!(w.is_empty(), "warnings: {w:?}");
    }

    #[test]
    fn accumulation_outside_loop_no_warning() {
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  total = total + 1.5\n  return total\nend",
        );
        assert!(w.is_empty(), "warnings: {w:?}");
    }

    #[test]
    fn accumulation_after_loop_on_same_acc_warns_once() {
        // The in-loop `total = total + 1.5` warns; the identical post-loop
        // statement on the SAME accumulator is a sibling of the `for`, not
        // inside it, so it must NOT warn. Pins that the `in_loop` flag does
        // not leak from a loop to statements that follow it.
        let w = warnings_for(
            "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total + 1.5\n  end\n  total = total + 1.5\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn non_accumulating_scalar_add_in_loop_no_warning() {
        // Guards the self-reference requirement: `r` does not appear in the
        // sum, so this is not accumulation (mutation-verified gap).
        let w = warnings_for(
            "function s(a: Scalar, b: Scalar): Scalar\n  let r: Scalar = 0.0\n  for i = 0, 3 do\n    r = a + b\n  end\n  return r\nend",
        );
        assert!(w.is_empty(), "warnings: {w:?}");
    }

    #[test]
    fn accumulation_in_for_in_warns() {
        let w = warnings_for(
            "function s(xs: Array<Scalar>): Scalar\n  let total: Scalar = 0.0\n  for x in xs do\n    total = total + x\n  end\n  return total\nend",
        );
        assert_eq!(w.len(), 1, "warnings: {w:?}");
    }

    #[test]
    fn warning_shape_label_and_note() {
        let src = "function s(): Scalar\n  let total: Scalar = 0.0\n  for i = 0, 3 do\n    total = total + 1.5\n  end\n  return total\nend";
        let w = warnings_for(src);
        assert_eq!(w[0].labels.len(), 1);
        assert_eq!(w[0].labels[0].1, "accumulator defined here");
        assert!(w[0].notes[0].contains("kahan_sum"));
        assert!(w[0].message.contains("floating-point accumulation"));
        let add_pos = src.find("total + 1.5").expect("addition in source");
        assert_eq!(
            w[0].span.start, add_pos,
            "primary span must be the addition expression"
        );
    }
}
