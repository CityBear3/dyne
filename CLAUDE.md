# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Dyne is a compiled programming language for computational physics (Hamiltonian mechanics, symplectic integration, unit-checked physical quantities). The repository contains:

- `docs/language-spec.md` — authoritative language specification (lexical structure, syntax, type system, semantics, stdlib overview). This is the contract the compiler must implement; when implementation and spec disagree, one of them is wrong.
- `docs/product-spec.md` — motivation and feature overview for end users.
- `compiler/` — the compiler, written in Rust (edition 2024), zero runtime dependencies. Stage 1 frontend (lexer, parser, AST, error model, CLI) is implemented; type checker, semantic analysis, and runtime are not yet built. Public API is `pub fn compile(source: &str) -> Result<Program, CompileError>` in `src/lib.rs`.
- `Makefile` — placeholder only (`clean` / `build` targets operating on an unused `build/` dir). The real build is cargo.
- `README.md` — top-level repository entry point.

## Common commands

All commands run from `compiler/` unless noted.

- Build: `cargo build`
- Run: `cargo run`
- Test (all): `cargo test`
- Test (single): `cargo test <name>` — e.g. `cargo test init_lexer`
- Lint: `cargo clippy`
- Format: `cargo fmt`

## Architecture notes

The Stage 1 frontend (lexer, parser, AST, error model) is implemented and tested. Subsequent phases (type checker, semantic analysis, interpreter/codegen) are not yet started. When implementing new phases, derive requirements from `docs/language-spec.md` and consume the existing AST defined in `compiler/src/ast/` rather than inferring from incidental code.

The AST already covers the full language (Stage 1-4 nodes are defined), but the parser only constructs Stage 1 nodes for now. Extending the parser to Stage 2 (struct / enum / match) and beyond should not require AST changes.

Language traits that shape compiler design and should be kept in mind when adding phases:

- **Block-terminated syntax** (`end` closes `function`/`if`/`for`/`while`/`match`/`struct`/`enum`; no braces, no semicolons). Statement boundaries are significant — newlines matter; the lexer/parser design must account for this.
- **Mandatory type annotations** on `let`, function parameters, and return types. The parser should treat missing annotations as an error, not fill in with inference.
- **Unit-annotated types** (`Scalar<kg>`, `Vec<3, m/s>`) are checked at compile time alongside regular types. Units are the *last* type parameter and are optional (omission = dimensionless). The type checker must carry unit information through arithmetic (e.g. multiplication propagates units).
- **Dimensional checking for `Vec<N>` / `Mat<M,N>`** happens at compile time — dimensions are part of the type, not a runtime attribute.
- **Exhaustive pattern matching** on `enum` (`Result`, `Option`, user-defined). Non-exhaustive `match` must be a compile error.
- **Implicit `Int → dimensionless Scalar`** conversion is allowed; conversion to a unit-annotated `Scalar` requires explicit handling. `Scalar → Int` always requires `to_int(...)`.
- **Strict evaluation, block scoping, pass-by-value** semantics (compiler may optimize copies internally, e.g. CoW).
- **Panics print stack traces**; NaN/infinity propagate per IEEE 754 by default, with an opt-in compiler flag to panic instead.
- **Compile-time precision warnings** are expected — the compiler analyzes floating-point addition patterns in loops and warns on rounding-error accumulation risk.

The standard library (automatic differentiation, symplectic integrators, `kahan_sum`, physical constants, nondimensionalization, `printf`, file I/O returning `Result`) is described in spec §7 but not yet implemented.