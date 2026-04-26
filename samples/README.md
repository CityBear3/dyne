# Samples

Small `.dy` programs that illustrate the language's syntax.

## Status

Stage 1 of the compiler implements the **frontend only** — lexer, parser, AST, and error model. The samples here are written against the spec and parse cleanly through the current frontend, but cannot yet be executed: the type checker, semantic analysis, and runtime are not implemented yet.

Treat these files as syntax demonstrations and as test fixtures (an integration test in `compiler/tests/samples.rs` parses every `.dy` file in this directory on every CI run, so they cannot bit-rot when the parser changes).

## Files

| File | Topic |
|---|---|
| `hello.dy` | Simplest program — a unit-annotated `Scalar` declaration |
| `harmonic_oscillator.dy` | 1D Hamiltonian function with `Scalar<unit>` parameters |
| `vector_ops.dy` | `Vec<3>` typing, indexing, and a `dot` function |
| `matrix_identity.dy` | Multi-line `Mat<3, 3>` literal with a trailing comma |
| `euler_step.dy` | `for` range loop driving a simple Euler integrator |

## Running

Once the runtime lands, you'll be able to:

```sh
cd compiler
cargo run -- ../samples/hello.dy
```

For now the same command will print `parsed N item(s)` if parsing succeeds, or a line/column-annotated diagnostic otherwise.
