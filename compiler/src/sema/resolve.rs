//! Name resolution: lexically-scoped symbol table + AST walker.

use std::collections::HashMap;

use crate::ast::{
    Block, Expr, ExprKind, ForStmt, FunctionDef, IfExpr, Item, LambdaBody, LambdaExpr, MatchArm,
    Pattern, PatternKind, Program, Stmt, StmtKind, WhileStmt,
};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::source::Span;

/// Maps every resolved AST identifier (by its NodeId) to the DefId it refers
/// to.
pub type ResolveTable = HashMap<NodeId, DefId>;

/// Metadata stored per definition. Stage 3a only records the kind and
/// declaration span; later stages will add signatures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionInfo {
    pub kind: DefKind,
    pub span: Span,
    pub name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefKind {
    Function,
    Struct,
    Enum,
    EnumVariant,
    TopLevelLet,
    LocalLet,
    Param,
    LoopVar,
    PatternBinding,
}

pub type DefinitionTable = HashMap<DefId, DefinitionInfo>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ScopeEntry {
    def_id: DefId,
    span: Span,
}

#[derive(Debug)]
pub(crate) struct SymbolTable {
    scopes: Vec<HashMap<String, ScopeEntry>>,
}

impl SymbolTable {
    pub(crate) fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    pub(crate) fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub(crate) fn exit_scope(&mut self) {
        debug_assert!(self.scopes.len() > 1, "cannot exit root scope");
        self.scopes.pop();
    }

    /// Insert a name into the current scope. On collision in the current
    /// scope, returns `Err(previous_span)` so the caller can build a
    /// "duplicate definition" diagnostic. Outer-scope shadowing is allowed
    /// and returns `Ok(())`.
    pub(crate) fn define(&mut self, name: String, def_id: DefId, span: Span) -> Result<(), Span> {
        let current = self.scopes.last_mut().expect("at least one scope");
        if let Some(prev) = current.get(&name) {
            return Err(prev.span);
        }
        current.insert(name, ScopeEntry { def_id, span });
        Ok(())
    }

    /// Resolve a name by walking scopes innermost-to-outermost.
    pub(crate) fn lookup(&self, name: &str) -> Option<DefId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|s| s.get(name).map(|e| e.def_id))
    }
}

pub(crate) struct Resolver {
    table: SymbolTable,
    next_def: u32,
    pub(crate) resolutions: ResolveTable,
    pub(crate) definitions: DefinitionTable,
    pub(crate) diagnostics: Vec<Diagnostic>,
}

impl Resolver {
    pub(crate) fn new() -> Self {
        Self {
            table: SymbolTable::new(),
            next_def: 0,
            resolutions: ResolveTable::new(),
            definitions: DefinitionTable::new(),
            diagnostics: Vec::new(),
        }
    }

    fn fresh_def(&mut self, kind: DefKind, name: String, span: Span) -> DefId {
        let id = DefId(self.next_def);
        self.next_def += 1;
        self.definitions
            .insert(id, DefinitionInfo { kind, span, name });
        id
    }

    fn define_or_report(&mut self, name: String, kind: DefKind, span: Span) -> Option<DefId> {
        let def_id = self.fresh_def(kind, name.clone(), span);
        match self.table.define(name.clone(), def_id, span) {
            Ok(()) => Some(def_id),
            Err(prev_span) => {
                self.diagnostics
                    .push(crate::sema::diag::duplicate_name(span, prev_span, &name));
                None
            }
        }
    }
}

/// Walk a Program and produce its resolution tables alongside any sema
/// diagnostics. Programs with undefined names produce diagnostics; well-
/// resolved programs return an empty `Vec<Diagnostic>`.
pub fn resolve_program(prog: &Program) -> (ResolveTable, DefinitionTable, Vec<Diagnostic>) {
    let mut r = Resolver::new();
    hoist_top_level(&mut r, prog);
    for item in &prog.items {
        resolve_item(&mut r, item);
    }
    (r.resolutions, r.definitions, r.diagnostics)
}

fn hoist_top_level(r: &mut Resolver, prog: &Program) {
    for item in &prog.items {
        match item {
            Item::Function(f) => {
                r.define_or_report(f.name.clone(), DefKind::Function, f.span);
            }
            Item::Struct(s) => {
                r.define_or_report(s.name.clone(), DefKind::Struct, s.span);
            }
            Item::Enum(e) => {
                r.define_or_report(e.name.clone(), DefKind::Enum, e.span);
                for variant in &e.variants {
                    r.define_or_report(variant.name.clone(), DefKind::EnumVariant, variant.span);
                }
            }
            Item::Let(l) => {
                // Top-level let: hoist the name. The LetStmt struct itself has
                // no span; use the init expression's span as the binding site.
                r.define_or_report(l.name.clone(), DefKind::TopLevelLet, l.init.span);
            }
            Item::Import(_) => { /* PR-3a: imports are no-ops */ }
        }
    }
}

fn resolve_item(r: &mut Resolver, item: &Item) {
    match item {
        Item::Function(f) => resolve_function(r, f),
        Item::Let(l) => {
            // Top-level let: only walk the RHS; the name was hoisted.
            resolve_expr(r, &l.init);
        }
        Item::Struct(_) | Item::Enum(_) | Item::Import(_) => {
            // PR-3a does not resolve type annotations or variant payloads.
            // Type-name resolution lands in PR-3b alongside Type → Ty
            // conversion.
        }
    }
}

fn resolve_function(r: &mut Resolver, f: &FunctionDef) {
    r.table.enter_scope();
    for p in &f.params {
        r.define_or_report(p.name.clone(), DefKind::Param, p.span);
    }
    resolve_block_no_scope(r, &f.body);
    r.table.exit_scope();
}

fn resolve_block(r: &mut Resolver, b: &Block) {
    r.table.enter_scope();
    for stmt in &b.stmts {
        resolve_stmt(r, stmt);
    }
    r.table.exit_scope();
}

/// Walk a block's statements without pushing a new scope. Used when the
/// caller already pushed a scope (function body shares its scope with the
/// param list; for-loop body shares the loop-var scope).
fn resolve_block_no_scope(r: &mut Resolver, b: &Block) {
    for stmt in &b.stmts {
        resolve_stmt(r, stmt);
    }
}

fn resolve_stmt(r: &mut Resolver, s: &Stmt) {
    match &s.kind {
        StmtKind::Let(l) => {
            // Walk the RHS in the *current* scope (let is non-recursive),
            // then introduce the name.
            resolve_expr(r, &l.init);
            r.define_or_report(l.name.clone(), DefKind::LocalLet, s.span);
        }
        StmtKind::Assign(name, expr) => {
            resolve_name_use(r, name, s.span, s.id);
            resolve_expr(r, expr);
        }
        StmtKind::Expr(expr) => resolve_expr(r, expr),
        StmtKind::Return(Some(expr)) => resolve_expr(r, expr),
        StmtKind::Return(None) => {}
        StmtKind::For(for_stmt) => resolve_for(r, for_stmt, s.span),
        StmtKind::While(w) => resolve_while(r, w),
    }
}

fn resolve_for(r: &mut Resolver, f: &ForStmt, outer_span: Span) {
    // ForStmt variants do not carry per-binding spans; fall back to the
    // outer Stmt span for loop-var binding sites. Pinning a precise span is
    // a quality improvement that can be revisited later.
    match f {
        ForStmt::Range {
            var,
            start,
            end,
            body,
        } => {
            resolve_expr(r, start);
            resolve_expr(r, end);
            r.table.enter_scope();
            r.define_or_report(var.clone(), DefKind::LoopVar, outer_span);
            resolve_block_no_scope(r, body);
            r.table.exit_scope();
        }
        ForStmt::Iter { var, iter, body } => {
            resolve_expr(r, iter);
            r.table.enter_scope();
            r.define_or_report(var.clone(), DefKind::LoopVar, outer_span);
            resolve_block_no_scope(r, body);
            r.table.exit_scope();
        }
        ForStmt::IterKV {
            key,
            value,
            iter,
            body,
        } => {
            resolve_expr(r, iter);
            r.table.enter_scope();
            r.define_or_report(key.clone(), DefKind::LoopVar, outer_span);
            r.define_or_report(value.clone(), DefKind::LoopVar, outer_span);
            resolve_block_no_scope(r, body);
            r.table.exit_scope();
        }
    }
}

fn resolve_while(r: &mut Resolver, w: &WhileStmt) {
    resolve_expr(r, &w.cond);
    resolve_block(r, &w.body);
}

fn resolve_expr(r: &mut Resolver, e: &Expr) {
    match &e.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::BoolLit(_) => {}
        ExprKind::Ident(name) => resolve_name_use(r, name, e.span, e.id),
        ExprKind::VecLit(items) => {
            for v in items {
                resolve_expr(r, v);
            }
        }
        ExprKind::MatLit(rows) => {
            for row in rows {
                for v in row {
                    resolve_expr(r, v);
                }
            }
        }
        ExprKind::BinOp(_, l, rr) => {
            resolve_expr(r, l);
            resolve_expr(r, rr);
        }
        ExprKind::UnaryOp(_, x) => resolve_expr(r, x),
        ExprKind::Call(callee, args) => {
            resolve_expr(r, callee);
            for a in args {
                resolve_expr(r, a);
            }
        }
        ExprKind::Index(b, i) => {
            resolve_expr(r, b);
            resolve_expr(r, i);
        }
        ExprKind::FieldAccess(b, _name) => {
            // Field name resolves in PR-3b/3c against the struct definition;
            // here we only walk the LHS.
            resolve_expr(r, b);
        }
        ExprKind::Lambda(l) => resolve_lambda(r, l),
        ExprKind::StructLit(name, fields) => {
            // The struct name resolves like an ordinary identifier (it was
            // hoisted into the root scope); field names are deferred.
            resolve_name_use(r, name, e.span, e.id);
            for (_fname, fexpr) in fields {
                resolve_expr(r, fexpr);
            }
        }
        ExprKind::If(if_expr) => resolve_if(r, if_expr),
        ExprKind::Match(scrut, arms) => {
            resolve_expr(r, scrut);
            for arm in arms {
                resolve_match_arm(r, arm);
            }
        }
        ExprKind::Block(b) => resolve_block(r, b),
    }
}

fn resolve_lambda(r: &mut Resolver, l: &LambdaExpr) {
    r.table.enter_scope();
    for p in &l.params {
        // LambdaExpr has no span; use each param's own span as its binding
        // site.
        r.define_or_report(p.name.clone(), DefKind::Param, p.span);
    }
    match &l.body {
        LambdaBody::Expr(e) => resolve_expr(r, e),
        LambdaBody::Block(b) => resolve_block_no_scope(r, b),
    }
    r.table.exit_scope();
}

fn resolve_if(r: &mut Resolver, i: &IfExpr) {
    resolve_expr(r, &i.cond);
    resolve_block(r, &i.then_block);
    for (cond, block) in &i.elseifs {
        resolve_expr(r, cond);
        resolve_block(r, block);
    }
    if let Some(else_block) = &i.else_block {
        resolve_block(r, else_block);
    }
}

fn resolve_match_arm(r: &mut Resolver, arm: &MatchArm) {
    r.table.enter_scope();
    bind_pattern(r, &arm.pattern);
    resolve_block_no_scope(r, &arm.body);
    r.table.exit_scope();
}

fn bind_pattern(r: &mut Resolver, p: &Pattern) {
    match &p.kind {
        PatternKind::Wildcard
        | PatternKind::IntLit(_)
        | PatternKind::BoolLit(_)
        | PatternKind::StrLit(_) => {}
        PatternKind::Ident(name) => {
            r.define_or_report(name.clone(), DefKind::PatternBinding, p.span);
        }
        PatternKind::Variant(ctor_name, sub_patterns) => {
            // Variant constructor must resolve to a DefId (the variant
            // hoisted at the top level by hoist_top_level). The reference
            // is recorded against the pattern's NodeId.
            resolve_name_use(r, ctor_name, p.span, p.id);
            for sub in sub_patterns {
                bind_pattern(r, sub);
            }
        }
    }
}

fn resolve_name_use(r: &mut Resolver, name: &str, span: Span, id: NodeId) {
    match r.table.lookup(name) {
        Some(def_id) => {
            r.resolutions.insert(id, def_id);
        }
        None => {
            r.diagnostics
                .push(crate::sema::diag::undefined_name(span, name));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::DefId;
    use crate::source::Span;

    fn span_at(start: u32, end: u32) -> Span {
        Span::new(start as usize, end as usize)
    }

    #[test]
    fn root_scope_lookup_returns_none_for_undefined_name() {
        let table = SymbolTable::new();
        assert_eq!(table.lookup("x"), None);
    }

    #[test]
    fn define_then_lookup_returns_def_id() {
        let mut table = SymbolTable::new();
        table.define("x".into(), DefId(7), span_at(0, 1)).unwrap();
        assert_eq!(table.lookup("x"), Some(DefId(7)));
    }

    #[test]
    fn exit_scope_drops_inner_definitions() {
        let mut table = SymbolTable::new();
        table.enter_scope();
        table.define("x".into(), DefId(1), span_at(0, 1)).unwrap();
        assert_eq!(table.lookup("x"), Some(DefId(1)));
        table.exit_scope();
        assert_eq!(table.lookup("x"), None);
    }

    #[test]
    fn same_scope_redefinition_returns_previous_span() {
        let mut table = SymbolTable::new();
        let first = span_at(0, 1);
        table.define("x".into(), DefId(1), first).unwrap();
        let err = table
            .define("x".into(), DefId(2), span_at(10, 11))
            .unwrap_err();
        assert_eq!(err, first);
    }

    #[test]
    fn outer_scope_shadowing_is_allowed_and_inner_wins() {
        let mut table = SymbolTable::new();
        table.define("x".into(), DefId(1), span_at(0, 1)).unwrap();
        table.enter_scope();
        table.define("x".into(), DefId(2), span_at(10, 11)).unwrap();
        assert_eq!(table.lookup("x"), Some(DefId(2)));
        table.exit_scope();
        assert_eq!(table.lookup("x"), Some(DefId(1)));
    }

    #[test]
    fn lookup_walks_multiple_scopes_innermost_first() {
        let mut table = SymbolTable::new();
        table
            .define("outer".into(), DefId(1), span_at(0, 5))
            .unwrap();
        table.enter_scope();
        table
            .define("inner".into(), DefId(2), span_at(10, 15))
            .unwrap();
        assert_eq!(table.lookup("outer"), Some(DefId(1)));
        assert_eq!(table.lookup("inner"), Some(DefId(2)));
    }

    use crate::ast::Program;
    use crate::lexer::tokenize;
    use crate::parser::parse;

    fn parse_src(src: &str) -> Program {
        parse(tokenize(src).unwrap()).unwrap()
    }

    #[test]
    fn resolve_empty_program_yields_no_diagnostics() {
        let prog = parse_src("");
        let (resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty());
        assert!(resolutions.is_empty());
    }

    #[test]
    fn resolve_top_level_let_then_use_in_function_body() {
        let src = "let k: Scalar = 0.5\nfunction f(): Scalar\n  return k\nend";
        let prog = parse_src(src);
        let (resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags);
        // The `k` reference inside f's body resolves to the top-level let.
        // Verify at least one resolution exists for the Ident.
        assert!(!resolutions.is_empty());
    }

    #[test]
    fn resolve_undefined_name_produces_sema_diagnostic() {
        let src = "function f(): Scalar\n  return undefined_var\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].phase, crate::diag::Phase::Sema);
        assert_eq!(diags[0].level, crate::diag::Level::Error);
        assert!(diags[0].message.contains("undefined_var"));
    }

    #[test]
    fn resolve_duplicate_top_level_let_produces_diagnostic() {
        let src = "let x: Int = 1\nlet x: Int = 2";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("`x`"));
        assert!(diags[0].message.contains("already defined"));
        assert!(!diags[0].labels.is_empty());
    }

    #[test]
    fn resolve_top_level_forward_reference_succeeds() {
        // f calls g; g is defined later. With hoisting, this resolves cleanly.
        let src = "function f(): Int\n  return g()\nend\nfunction g(): Int\n  return 0\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty());
    }

    #[test]
    fn resolve_function_param_in_body() {
        let src = "function f(x: Scalar): Scalar\n  return x\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty());
    }

    #[test]
    fn resolve_block_local_let_visible_inside_block_only() {
        let src = "function f(): Int\n  let y: Int = 1\n  return y\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_for_range_loop_var_visible_in_body() {
        let src = "function sum(n: Int): Int\n  let total: Int = 0\n  for i = 0, n do\n    total = total + i\n  end\n  return total\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_enum_variant_used_in_match_arm() {
        let src = "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(m: Maybe): Int\n  return match m\n    case Just(x) then x\n    case Nothing then 0\n  end\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_typo_in_match_pattern_constructor_produces_diagnostic() {
        let src = "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(m: Maybe): Int\n  return match m\n    case Jsut(x) then x\n    case Nothing then 0\n  end\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.iter().any(|d| d.message.contains("Jsut")));
    }
}
