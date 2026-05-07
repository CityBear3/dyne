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

    /// Insert `name` into the current scope and record its definition. On
    /// same-scope collision, push a duplicate-name diagnostic and return
    /// `None` *without* allocating a fresh `DefId` — the `definitions` table
    /// must only contain entries reachable through some scope.
    fn define_or_report(&mut self, name: String, kind: DefKind, span: Span) -> Option<DefId> {
        let def_id = DefId(self.next_def);
        match self.table.define(name.clone(), def_id, span) {
            Ok(()) => {
                self.next_def += 1;
                self.definitions
                    .insert(def_id, DefinitionInfo { kind, span, name });
                Some(def_id)
            }
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
            // `Item::Let` is intentionally NOT hoisted: top-level `let` has
            // the same "RHS first, then introduce" semantics as a local
            // `let`, mirroring Rust/OCaml. This makes `let x: Int = x + 1`
            // a sema error (undefined `x`) rather than a runtime read of
            // uninitialized storage. Forward references between top-level
            // lets are correspondingly disallowed; functions remain forward-
            // referenceable through the hoist above.
            Item::Let(_) => {}
            Item::Import(_) => { /* PR-3a: imports are no-ops */ }
        }
    }
}

fn resolve_item(r: &mut Resolver, item: &Item) {
    match item {
        Item::Function(f) => resolve_function(r, f),
        Item::Let(l) => {
            // Top-level let: walk the type annotation, then walk the RHS in
            // the current (root) scope, THEN introduce the binding. Mirrors
            // local let semantics.
            resolve_type_annotation(r, &l.ty);
            resolve_expr(r, &l.init);
            r.define_or_report(l.name.clone(), DefKind::TopLevelLet, l.init.span);
        }
        Item::Struct(s) => {
            for field in &s.fields {
                resolve_type_annotation(r, &field.ty);
            }
        }
        Item::Enum(e) => {
            // Generic enum payloads reference the enum's type parameters
            // (e.g. `Ok(T)` inside `enum Result<T, E>`). Type-parameter
            // scoping lands with PR-3c's generic instantiation; until then,
            // skip the payload walk for generic enums to avoid spurious
            // undefined-name diagnostics for T/E. Non-generic enums still
            // get their concrete payload types resolved.
            if e.type_params.is_empty() {
                for variant in &e.variants {
                    for payload_ty in &variant.payload {
                        resolve_type_annotation(r, payload_ty);
                    }
                }
            }
        }
        Item::Import(_) => {
            // PR-3a: imports are no-ops.
        }
    }
}

fn resolve_function(r: &mut Resolver, f: &FunctionDef) {
    r.table.enter_scope();
    for p in &f.params {
        r.define_or_report(p.name.clone(), DefKind::Param, p.span);
        resolve_type_annotation(r, &p.ty);
    }
    resolve_type_annotation(r, &f.return_ty);
    resolve_stmts(r, &f.body.stmts);
    r.table.exit_scope();
}

fn resolve_block(r: &mut Resolver, b: &Block) {
    r.table.enter_scope();
    for stmt in &b.stmts {
        resolve_stmt(r, stmt);
    }
    r.table.exit_scope();
}

/// Walk a slice of statements without pushing a new scope. Used when the
/// caller already manages the surrounding scope (function body shares its
/// scope with the param list; for-loop body shares the loop-var scope;
/// match-arm body shares the pattern-binding scope).
fn resolve_stmts(r: &mut Resolver, stmts: &[Stmt]) {
    for stmt in stmts {
        resolve_stmt(r, stmt);
    }
}

fn resolve_stmt(r: &mut Resolver, s: &Stmt) {
    match &s.kind {
        StmtKind::Let(l) => {
            // Walk the type annotation, then the RHS in the *current* scope
            // (let is non-recursive), then introduce the name.
            resolve_type_annotation(r, &l.ty);
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
            resolve_stmts(r, &body.stmts);
            r.table.exit_scope();
        }
        ForStmt::Iter { var, iter, body } => {
            resolve_expr(r, iter);
            r.table.enter_scope();
            r.define_or_report(var.clone(), DefKind::LoopVar, outer_span);
            resolve_stmts(r, &body.stmts);
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
            resolve_stmts(r, &body.stmts);
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

// NOTE: this function is currently unreachable from parsed input — the Stage
// 1/2 parser does not yet construct `ExprKind::Lambda` nodes (no surface
// syntax for `(x) -> x + 1` or similar). The walk is in place so that when
// lambda parsing lands (likely PR-3b/3c alongside generic-function support
// or first-class function values), name resolution Just Works without
// further changes here. End-to-end tests for lambda capture-at-definition-
// site semantics will be added at that point; until then this function is
// covered only by inspection.
fn resolve_lambda(r: &mut Resolver, l: &LambdaExpr) {
    r.table.enter_scope();
    for p in &l.params {
        // LambdaExpr has no span; use each param's own span as its binding
        // site.
        r.define_or_report(p.name.clone(), DefKind::Param, p.span);
    }
    match &l.body {
        LambdaBody::Expr(e) => resolve_expr(r, e),
        LambdaBody::Block(b) => resolve_stmts(r, &b.stmts),
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
    resolve_stmts(r, &arm.body.stmts);
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

/// Walk a type annotation, recording resolutions for user-defined type names.
/// Built-in type names (`Int`/`Bool`/`String`/`Scalar`/`Vec`/`Mat`/`Array`/`Dict`)
/// have no DefId and are skipped here; `lower_type` dispatches them by string.
fn resolve_type_annotation(r: &mut Resolver, ty: &crate::ast::Type) {
    use crate::ast::{TypeArg, TypeKind};
    match &ty.kind {
        TypeKind::Named(name) => {
            if !is_builtin_type_name(name) {
                resolve_name_use(r, name, ty.span, ty.id);
            }
        }
        TypeKind::Generic(name, args) => {
            if !is_builtin_type_name(name) {
                resolve_name_use(r, name, ty.span, ty.id);
            }
            // For Scalar/Vec/Mat the trailing/all args are unit or size
            // positions, never real type positions. The parser ambiguously
            // emits TypeArg::Type(Named("kg")) for single-atom units (it
            // can't disambiguate "kg" from a type name without context), so
            // skip recursion into those positions. lower_type silently
            // strips them per Option β.
            let unit_or_size_only = matches!(name.as_str(), "Scalar" | "Vec" | "Mat");
            if !unit_or_size_only {
                for arg in args {
                    match arg {
                        TypeArg::Type(t) => resolve_type_annotation(r, t),
                        TypeArg::Int(_) => {}
                        TypeArg::Unit(u) => resolve_unit_expr(r, u),
                    }
                }
            }
        }
        TypeKind::Function(args, ret) => {
            for a in args {
                resolve_type_annotation(r, a);
            }
            resolve_type_annotation(r, ret);
        }
    }
}

fn is_builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "Int" | "Bool" | "String" | "Scalar" | "Vec" | "Mat" | "Array" | "Dict"
    )
}

fn resolve_unit_expr(_r: &mut Resolver, _u: &crate::ast::UnitExpr) {
    // PR-3d resolves unit names. PR-3b's resolver does not visit unit atoms;
    // lower_type's silent-strip behavior (Option β) means unit args are
    // semantically inert in 3b.
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
    use crate::ast::Program;
    use crate::ids::DefId;
    use crate::lexer::tokenize;
    use crate::parser::parse;
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
        // The duplicate carries exactly one secondary label pointing at the
        // prior definition's site, with the standard "previously defined"
        // text — pin both so a regression that drops the label or changes
        // its message fails loudly.
        assert_eq!(diags[0].labels.len(), 1);
        assert!(diags[0].labels[0].1.contains("previously defined"));
    }

    #[test]
    fn resolve_duplicate_definition_does_not_leak_orphan_def_id() {
        // Every entry in the definitions table must be reachable through
        // resolutions or by name lookup; rejected duplicates must not
        // leave ghost entries (otherwise PR-3b's type-check loop would
        // visit unbound DefIds).
        let src = "let x: Int = 1\nlet x: Int = 2";
        let prog = parse_src(src);
        let (_resolutions, defs, _diags) = resolve_program(&prog);
        assert_eq!(
            defs.len(),
            1,
            "rejected duplicate must not leave an orphan DefId in definitions, got {:?}",
            defs
        );
    }

    #[test]
    fn resolve_top_level_let_self_reference_is_undefined() {
        // Top-level let is non-recursive: the name is not visible to its
        // own RHS. Without this rule, codegen would have to read from
        // uninitialized storage at runtime.
        let src = "let x: Int = x + 1";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("undefined name `x`")),
            "expected undefined-name diag for self-referencing top-level let, got {:?}",
            diags
        );
    }

    #[test]
    fn resolve_top_level_let_forward_reference_is_undefined() {
        // Forward references between top-level lets are NOT allowed (only
        // function/struct/enum names are hoisted). `b` has not been defined
        // when `let a` is resolved.
        let src = "let a: Int = b\nlet b: Int = 1";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("undefined name `b`")),
            "expected undefined-name diag for forward let reference, got {:?}",
            diags
        );
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
    fn resolve_for_loop_var_collides_with_let_in_body() {
        let src =
            "function f(): Int\n  for i = 0, 10 do\n    let i: Int = 5\n  end\n  return 0\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(
            diags.len(),
            1,
            "expected exactly one duplicate-name diag, got {:?}",
            diags
        );
        assert!(diags[0].message.contains("`i`"));
        assert!(diags[0].message.contains("already defined"));
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

    // ----- Coverage gaps surfaced by /review (test-coverage-reviewer) -----
    // The following tests pin resolver branches and behaviors that the
    // initial Task 4 test list missed.

    #[test]
    fn resolve_for_iter_loop_var_visible_in_body() {
        // Parser produces ForStmt::Iter for `for x in iter do ... end`.
        let src = "function f(xs: Array<Int>): Int\n  let total: Int = 0\n  for x in xs do\n    total = total + x\n  end\n  return total\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_for_iterkv_loop_vars_visible_in_body() {
        // Parser produces ForStmt::IterKV for `for k, v in pairs do ... end`.
        let src = "function f(pairs: Dict<Int, Int>): Int\n  let total: Int = 0\n  for k, v in pairs do\n    total = total + k + v\n  end\n  return total\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_while_condition_uses_param_and_body_can_assign() {
        // Pins resolve_while: cond resolves outer name; body's Assign
        // statement resolves both LHS and RHS in the surrounding scope.
        let src = "function f(n: Int): Int\n  let i: Int = 0\n  while i < n do\n    i = i + 1\n  end\n  return i\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_assign_to_undefined_name_produces_diagnostic() {
        // The Assign LHS goes through resolve_name_use; an undefined LHS
        // must produce a sema diagnostic.
        let src = "function f(): Int\n  undefined = 1\n  return 0\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags.iter().any(|d| d.message.contains("undefined")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn resolve_struct_literal_name_resolves_to_definition() {
        // resolve_expr's StructLit arm calls resolve_name_use on the struct
        // constructor; this test pins both the positive path...
        let src =
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Point { x: 1.0, y: 2.0 }";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_typo_in_struct_literal_name_produces_diagnostic() {
        // ...and the negative path: a typo in the struct constructor name
        // must produce an undefined-name diagnostic.
        let src =
            "struct Point\n  x: Scalar\n  y: Scalar\nend\nlet p: Point = Pint { x: 1.0, y: 2.0 }";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags.iter().any(|d| d.message.contains("Pint")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn resolve_pattern_binding_does_not_leak_across_match_arms() {
        // resolve_match_arm pushes a fresh scope per arm; a pattern binding
        // in arm 1 must NOT be visible in arm 2.
        let src = "enum Maybe\n  Just(Int)\n  Nothing\nend\nfunction f(m: Maybe): Int\n  return match m\n    case Just(x) then 0\n    case Nothing then x\n  end\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("undefined name `x`")),
            "expected x to be undefined in second arm, got {:?}",
            diags
        );
    }

    #[test]
    fn resolve_multiple_lets_chain_in_dependency_order() {
        // Each top-level let walks its RHS first, then introduces its name,
        // so a later let can refer to an earlier one (forward refs across
        // top-level lets are still rejected — covered separately).
        let src = "let a: Int = 1\nlet b: Int = a + 1";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_duplicate_function_name_produces_diagnostic() {
        // Both functions go through hoist_top_level → define_or_report;
        // the second produces a duplicate-name diagnostic.
        let src = "function f(): Int\n  return 0\nend\nfunction f(): Int\n  return 1\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("`f`"));
    }

    #[test]
    fn resolve_function_then_let_with_same_name_collides() {
        // Cross-kind same-name collision at top level: pins the "single
        // namespace at top level" invariant.
        let src = "function foo(): Int\n  return 0\nend\nlet foo: Int = 1";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags.iter().any(|d| d.message.contains("`foo`")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn resolve_let_then_function_with_same_name_collides() {
        // Same as above, opposite ordering. Note: hoist_top_level runs
        // first and registers the function; then resolve_item walks the
        // top-level let, whose name collides with the already-registered
        // function. So the diag fires on the let.
        let src = "let foo: Int = 1\nfunction foo(): Int\n  return 0\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(
            diags.iter().any(|d| d.message.contains("`foo`")),
            "diags: {:?}",
            diags
        );
    }

    #[test]
    fn resolve_same_scope_let_let_inside_block_collides() {
        // Two lets with the same name inside a function body share a
        // scope (the function body scope) and must collide.
        let src = "function f(): Int\n  let x: Int = 1\n  let x: Int = 2\n  return x\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("`x`"));
    }

    #[test]
    fn resolve_param_let_collision_in_function_body() {
        // Function params and the function body share a scope (DD line 197);
        // a let with the same name as a param must collide.
        let src = "function f(x: Int): Int\n  let x: Int = 1\n  return x\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("`x`"));
    }

    // ----- PR-3b Task 2: type-annotation walk -----

    #[test]
    fn resolve_struct_field_type_resolves_user_struct() {
        let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nstruct Line\n  start: Point\n  end_pt: Point\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_undefined_struct_in_type_annotation_diag() {
        let src = "let p: Point = 0";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        // Pin no-cascade: a single undefined type name in a single
        // annotation must produce exactly one diagnostic.
        assert_eq!(diags.len(), 1, "diags: {:?}", diags);
        assert!(
            diags[0].message.contains("Point"),
            "msg: {}",
            diags[0].message
        );
    }

    #[test]
    fn resolve_builtin_type_names_are_skipped() {
        // None of these built-ins should produce undefined-name diagnostics
        // even though no DefId exists for them.
        let src = "function f(x: Int, y: Scalar): Bool\n  return true\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_function_param_type_annotation_resolves() {
        let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nfunction f(p: Point): Point\n  return p\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }

    #[test]
    fn resolve_enum_variant_payload_type_resolves() {
        let src = "struct Point\n  x: Scalar\n  y: Scalar\nend\nenum Shape\n  Circle(Point)\n  Empty\nend";
        let prog = parse_src(src);
        let (_resolutions, _defs, diags) = resolve_program(&prog);
        assert!(diags.is_empty(), "diags: {:?}", diags);
    }
}
