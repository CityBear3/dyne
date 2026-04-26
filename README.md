[![CI](https://github.com/CityBear3/dyne/actions/workflows/ci.yml/badge.svg)](https://github.com/CityBear3/dyne/actions/workflows/ci.yml)

# Dyne

A compiled programming language for computational physics.

The name comes from the cgs unit of force — a fitting choice for a language whose type system carries physical units throughout.

## Status

**Early development.** The compiler frontend (lexer, parser, AST) is implemented for the Stage 1 subset of the language: type annotations including units, `let` bindings, function definitions, expressions, control flow, and `Vec`/`Mat` literals. Type checking, semantic analysis, and runtime are not yet built.

Source files use the `.dy` extension.

## Goals

- **First-class vectors and matrices** with compile-time dimension checking (`Vec<3>`, `Mat<2,3>`)
- **Automatic differentiation** — define a scalar Hamiltonian and have the equations of motion derived without manual partial derivatives
- **Compile-time unit checking** — physical quantities carry units (`Scalar<kg>`, `Vec<3, m/s>`), dimensional mismatches caught before runtime
- **Built-in symplectic integrators** — symplectic Euler, Stormer-Verlet, and 4th-order methods, in the standard library
- **Nondimensionalization** — transform equations into dimensionless form by specifying characteristic scales
- **Beginner-friendly syntax** — Lua-inspired block structure with `end` keywords; no braces, no semicolons

See [docs/product-spec.md](docs/product-spec.md) for motivation and [docs/language-spec.md](docs/language-spec.md) for the full specification.

## Build and Run

The compiler is a Rust 2024 crate with zero runtime dependencies. From `compiler/`:

```sh
cargo build
cargo test
cargo run -- path/to/source.dy
```

`cargo run` parses the source file and prints the number of top-level items, or a line/column-annotated diagnostic on a lex/parse error.

## Repository Layout

- `docs/` — language specification, product spec, and design docs
- `compiler/` — Rust implementation
  - `src/lib.rs` — `pub fn compile(source: &str) -> Result<Program, CompileError>`
  - `src/main.rs` — CLI entry point
