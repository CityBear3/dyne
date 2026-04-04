# Calculator

## What is Calculator?

Calculator is a compiled programming language designed for computational physics. It lets physicists and students write simulations the way they think about physics — in terms of Hamiltonians, vectors, and units — rather than fighting with generic arrays, manual differentiation, and boilerplate integration code.

## Motivation

Physics simulations are commonly written in Python with JAX/NumPy, MATLAB, or Fortran. While these tools are powerful, they force physicists to translate their mathematical thinking into programming constructs that don't match the structure of the physics.

Consider deriving equations of motion from a Hamiltonian. In Python, this requires computing partial derivatives one by one for each degree of freedom, manually concatenating the results into arrays, and losing all type-level distinction between position, momentum, and force. A 2D Henon-Heiles system needs four separate gradient calls and explicit array assembly. Scale to higher dimensions, and the code grows linearly with no structural guarantee that you haven't mixed up q and p.

Symplectic integrators — essential for preserving the geometric structure of Hamiltonian systems — must be reimplemented as boilerplate for every new project.

Calculator eliminates this friction. Write a Hamiltonian, and the equations of motion are derived automatically. Vectors carry their dimension in the type. Physical units are checked at compile time. Symplectic integration is a standard library call, not a copy-paste ritual.

## Key Features

- **First-class vectors and matrices** with compile-time dimension checking (`Vec<3>`, `Mat<2,3>`)
- **Automatic differentiation** — define a scalar function and compute its gradient; Hamilton's canonical equations are derived without manual partial derivatives
- **Compile-time unit checking** — physical quantities carry units (`Scalar<kg>`, `Vec<3, m/s>`), and dimensional mismatches are caught before runtime
- **Built-in symplectic integrators** — symplectic Euler, Stormer-Verlet, and 4th-order methods available out of the box
- **Nondimensionalization** — transform equations into dimensionless form by specifying characteristic scales
- **Physical constants** — fundamental constants provided as unit-annotated values in the standard library
- **Beginner-friendly syntax** — Lua-inspired block structure with `end` keywords, no braces, no semicolons

## Technical Details

- Compiled language
- Compiler implemented in Rust
- SI, CGS, and Gaussian unit systems provided out of the box

## Documentation

- [Language Specification](language-spec.md)

## Contributing

Calculator is open source. Contributions are welcome — whether language design feedback, compiler development, standard library implementation, or documentation.