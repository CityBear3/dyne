//! Lexically-scoped symbol table for name resolution.

#![allow(dead_code)] // SymbolTable is consumed by Task 4 (resolve_program).

use std::collections::HashMap;

use crate::ids::DefId;
use crate::source::Span;

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
}
