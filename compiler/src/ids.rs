//! Numeric identifiers used by the compiler's middle-end.
//!
//! `NodeId` is allocated by the parser and attached to every span-bearing AST
//! node. `DefId` is allocated by name resolution for each named definition
//! (function, struct, enum, top-level let, enum variant). Both are opaque
//! `u32` newtypes — only `sema` may inspect their inner values.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefId(pub u32);
