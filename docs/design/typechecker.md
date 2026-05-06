# Design Doc: Stage 3 — Type Checker (Semantic Analysis)

**Author:** CityBear3
**Date:** 2026-05-04
**Status:** Draft (decisions confirmed during /design-discussion on 2026-05-03/04)

## Context and Scope

Stages 1 and 2 of the dyne compiler — the lexer, parser, AST, and command-line interface — are complete and merged into `main` at HEAD `7b7e8f1`, with 193 tests passing. The AST already carries every node variant the language requires (Stage 1–4), but only Stage 1–2 nodes are constructed by the parser; the type system, semantic analysis, and runtime have not been built. This document describes Stage 3: the type checker and supporting semantic analysis.

The type checker is the first phase that consumes the parsed AST and produces an annotated artifact for downstream phases. It is also the first phase that touches the language's distinguishing features: unit-annotated types, compile-time dimension checking, and exhaustive pattern matching on enums. Getting its representation and architecture right shapes the rest of the compiler, including any future intermediate representation introduced for code generation.

### Goals

The type checker must implement the semantic rules described in `docs/language-spec.md` §4 (Type System) and §6 (Compiler Features). Concretely:

- All `let` bindings, function parameters, and return types are annotated by the parser. The checker verifies that each declared annotation is satisfied by the expression it bounds, and reports a diagnostic when it is not.
- Implicit conversion from `Int` to dimensionless `Scalar` is permitted; conversion to a unit-annotated `Scalar` requires the implicit-conversion path to fail and is reported as a type error. The reverse direction (`Scalar → Int`) requires an explicit `to_int(...)` call and is rejected when written implicitly.
- Operators carry through unit information. Multiplication of two unit-annotated `Scalar` values produces a `Scalar` whose dimension is the sum of the operand dimensions; division is the difference; addition and subtraction require operand dimensions to match; powers of integer exponents are accepted, fractional exponents are rejected.
- `Vec<N>` and `Mat<M, N>` carry their dimensions in the type. Operations that require dimensional consistency (vector addition, matrix-vector multiplication, etc.) are checked at compile time.
- `match` expressions on `enum` types are required to be exhaustive. Missing variants are reported.
- `Result<T, E>` and `Option<T>` are provided as built-in generic enums. User-defined enums with type parameters are supported. Type variables introduced by an enum's parameter list are instantiated at use sites; the local unification machinery handles inference at variant constructor calls and across `match` arms.
- The compiler emits warnings for floating-point summation patterns inside loops that risk rounding-error accumulation, as described in spec §6.1.

### Non-Goals

The following are deliberately out of scope for Stage 3 and are deferred to later stages or future work:

- **User-defined generic functions.** The spec does not require them, and the bidirectional checker described below does not perform Hindley-Milner-style generalization. When generic functions become necessary (for example, to type a user-implemented `kahan_sum<T>`), the migration adds a generalization phase to the existing unification machinery; the rest of the checker is unaffected.
- **Rational unit exponents.** Common physics in dyne's intended domain (Hamiltonian mechanics, symplectic integration) uses integer exponents only. Use cases such as noise spectral density (`V/√Hz`) require rational exponents but are uncommon enough to defer. The internal `Dimension` type is encapsulated so a future migration from `i8` to a rational representation does not propagate through the public API.
- **User-defined unit systems.** SI base units, plus a hard-coded set of derived units (`N`, `J`, `Hz`, `Pa`, `W`, `V`, etc.) and the CGS / Gaussian conversion tables required by spec §4.5, are sufficient for the initial release. The spec already defers user-defined systems to "future".
- **Code generation.** Stage 4 introduces a runtime (interpreter or codegen). The type checker's output (`TypedProgram`) is the contract between Stage 3 and Stage 4, but Stage 4's internal representation is independent.
- **Incremental compilation.** `NodeId`s are stable within a single compilation unit, but no effort is made to keep them stable across edits. Adding incremental compilation would later require a stable identifier scheme (similar to rustc's `LocalDefId`).

## Overview

Stage 3 is delivered as five sequential pull requests (3a–3e), preceded by one preparatory refactor PR that renames the existing `CompileError` type to a richer `Diagnostic`. Each PR produces a working compiler that accepts a strictly larger language than its predecessor.

The 3a foundation introduces the side-table infrastructure (`NodeId` and `DefId`), name resolution, and the entry point `pub fn check(prog: Program) -> Result<TypedProgram, Vec<Diagnostic>>`. After 3a the compiler can reject programs with undefined names. 3b adds the basic type checker for primitives, operators, function calls, `let` bindings, and `Vec` / `Mat` dimension checking, with units treated as zero-dimensional (everything is dimensionless). 3c extends the checker with generic enums and exhaustive pattern matching. 3d introduces the `Dimension` representation and threads units through every type rule. 3e provides the standard library's type signatures, polishes diagnostic output, and adds the spec §6.1 precision-warning analysis.

The architectural choice that shapes the rest of the document is the **side-table representation**: AST nodes are extended with a `NodeId(u32)` field at parse time, and all later phases store annotations in tables keyed by `NodeId`. This keeps the parser AST as a snapshot of the source, allows multiple independent annotation passes (type table, resolution table, future precision-risk table) to coexist orthogonally, and avoids the duplication cost of mirroring the AST into a separate typed tree.

The type checker uses **bidirectional checking with local unification** rather than full Hindley-Milner inference. Because all bindings, parameters, and return types are annotated, full inference is unnecessary; the only places where the checker must propagate type information across multiple expressions are enum constructor calls and `match` arms. A small unification table (without let-generalization) handles both. This sits between the simplicity of pure bidirectional checking and the generality of HM, and admits a later upgrade to HM if user-defined generic functions are added.

Units are represented as a **fixed-size integer dimension vector** over the seven SI base dimensions. Equivalence becomes vector equality, multiplication is pointwise addition of exponents, and CGS / Gaussian conversion is a scale factor folded into literal values at parse time. The vector representation is encapsulated behind a `Dimension` newtype with method-only access; a future migration to rational exponents changes the inside of `ty.rs` without affecting the rest of the compiler.

## Detailed Design

### Slice strategy

Stage 3 is decomposed into the following PRs, executed in order:

**PR-0 (preparatory refactor): Rename `CompileError` to `Diagnostic`.** This is a pure renaming of `compiler/src/error.rs` to `compiler/src/diag.rs`, plus the addition of `Level`, `labels`, and `notes` fields described in the Error Model subsection below. No behavior change; existing 188 tests remain green. This PR is small (roughly 30–50 lines of mechanical rename plus the field additions) and lands first to keep 3a focused on new functionality rather than refactoring.

**PR-3a: Foundation and name resolution.** This PR introduces `compiler/src/sema.rs` (entry point) and `compiler/src/sema/{ty.rs, resolve.rs, diag.rs}`. It adds `NodeId` and `DefId` types in `compiler/src/sema/ty.rs` (or a dedicated `ids.rs`), wires a `next_node_id` counter into the parser, and populates a `NodeId` field on every span-bearing AST node. A `SymbolTable` resolves identifiers to `DefId`s; programs with undefined names are rejected with a diagnostic. The entry point is `pub fn check(prog: Program) -> Result<TypedProgram, Vec<Diagnostic>>`, but at this stage `TypedProgram::types` is empty — only the resolution table is populated.

**PR-3b: Basic type checking (no units).** This PR adds `compiler/src/sema/check.rs` and `compiler/src/sema/unify.rs`. The `Ty` enum is implemented; a bidirectional check assigns types to every expression and verifies declared annotations. `Vec<N>` / `Mat<M, N>` dimension consistency is enforced. Units are present in the type but always `Dimension::ZERO` — every literal is dimensionless, and any user code that attempts to write a non-`ZERO` dimension is rejected as "units not yet supported" until 3d. `Int → Scalar` implicit conversion is enabled; `Scalar → Int` requires `to_int(...)`. Operator type rules (arithmetic, comparison, logical) are implemented for the dimensionless case.

**PR-3c: Generics and match exhaustiveness.** This PR adds `compiler/src/sema/exhaust.rs`. The unification machinery from 3b is exercised by enum constructor calls (`Some(x)`, `Ok(value)`) and by `match` arm type unification. Exhaustiveness checking enumerates all variants of the matched enum's definition and reports any uncovered variant. `Result<T, E>` and `Option<T>` are added to the symbol table as built-in enum definitions during checker initialization.

**PR-3d: Units (dimensions).** This PR replaces every `Dimension::ZERO` placeholder from 3b with the actual dimension produced by the program. The `Dimension` type's API gains pointwise arithmetic (`mul`, `div`, `pow`) and the operator type rules from 3b are extended to thread dimensions through. `Scalar<kg>` is now an actual unit-annotated type, and dimension mismatches in addition / subtraction / vector operations produce diagnostics. A small built-in table maps unit names (`kg`, `m`, `s`, etc., plus common derived units like `N`, `J`) to canonical `Dimension` values; the `parse_unit_expr` parser output is converted to `Dimension` during type checking.

**PR-3e: Standard library types, diagnostics polish, precision warnings.** This PR adds `compiler/src/sema/precision.rs` and the spec §7 standard library function type signatures (declared as built-in `DefId`s in the symbol table, similar to the built-in enums in 3c). Diagnostics gain secondary span labels and notes throughout the checker. Spec §6.1 precision warnings are emitted by analyzing floating-point addition patterns within loop bodies — see the Precision Warning Detection subsection below.

Each PR is shipped behind its own worktree (`.claude/worktrees/<branch>/`), branched from the latest `main`. The branch names are `diagnostic-rename`, `stage3a-foundation`, `stage3b-typecheck`, `stage3c-generics`, `stage3d-units`, and `stage3e-stdlib-diag`.

### AST integration via side-tables

Every span-bearing AST node carries a `NodeId(u32)` allocated by the parser. A `NodeId` is unique within a compilation unit; reserving zero as a sentinel is unnecessary because the parser allocates IDs eagerly during construction.

Definitions — `function`, `struct`, `enum`, and top-level `let` bindings — receive an additional `DefId(u32)`. A `DefId` is the resolution-table value: when an identifier is resolved to its definition, the resolution table records `NodeId → DefId`. Type information is then keyed by `DefId` for definitions and by `NodeId` for expressions.

The `TypedProgram` wrapper aggregates the program with all its annotation tables:

```rust
pub struct TypedProgram {
    pub program: Program,
    pub types: TypeTable,                    // NodeId -> Ty
    pub resolutions: ResolveTable,           // NodeId -> DefId
    pub definitions: DefinitionTable,        // DefId -> Ty (for function signatures, enum types, etc.)
}
```

`TypedProgram` is constructed only by `sema::check`; its private constructor enforces the phase boundary at compile time. Stage 4 will accept a `&TypedProgram` rather than a `Program`, and Rust's type system guarantees that no caller can skip the type-checking phase.

Annotations from later phases (precision warnings, future borrow analysis, future constant folding) are added as additional fields on `TypedProgram` without affecting existing tables.

### Type representation

The internal `Ty` enum represents resolved, post-checking types. It is distinct from the AST `Type` (which captures the surface syntax the user wrote): converting `Type → Ty` is part of name resolution and type checking.

```rust
pub enum Ty {
    Int,
    Scalar(Dimension),
    Bool,
    String,
    Vec(usize, Dimension),       // size N, element unit
    Mat(usize, usize),            // rows × cols (dimensionless per spec §4.4)
    Array(Box<Ty>),
    Dict(Box<Ty>, Box<Ty>),
    Function(Vec<Ty>, Box<Ty>),
    Struct(DefId),
    Enum(DefId, Vec<Ty>),         // DefId + instantiated type arguments
    Var(TypeVarId),               // unification variable
    Error,                         // sentinel for already-reported errors
}
```

`Scalar` and `Vec` always carry a `Dimension`. The dimensionless case is represented by `Dimension::ZERO` rather than `Option<Dimension>` to keep pattern matching uniform. `Mat` does not carry a dimension because the spec specifies matrices as dimensionless. `Array` and `Dict` containers are themselves dimensionless; if the contained `Ty` is unit-annotated, the unit lives on the element type.

`Var(TypeVarId)` is introduced when an enum constructor is encountered with insufficient information to instantiate its type parameters, or when match arm types must be unified before all arms have been processed. After unification, every reachable `Var` is replaced by its solution; any `Var` that survives substitution indicates an inference failure and is reported as a diagnostic.

`Error` is the recovery sentinel. Once an expression produces a diagnostic, its node's type becomes `Ty::Error`. Subsequent rules treat `Ty::Error` as compatible with any type, suppressing cascade diagnostics that would otherwise drown the original error.

### Dimension representation

A `Dimension` is a fixed-size integer vector over the seven SI base dimensions:

```rust
pub struct Dimension([i8; 7]);   // [length, mass, time, current, temperature, amount, luminous]
```

The array is private. Operations are exposed as methods (`mul`, `div`, `pow`, `is_dimensionless`, `format_si`) so that future work — for example, migrating `i8` to a `Rational` type to support fractional exponents — affects only `ty.rs` and not callers.

A small built-in unit registry maps unit names to `Dimension` values. SI base units are encoded directly (`m → [1, 0, 0, 0, 0, 0, 0]`, etc.). Derived units expand to their base form (`N → [1, 1, -2, 0, 0, 0, 0]` because `N = kg·m·s⁻²`). CGS and Gaussian unit names share the same dimension vectors as their SI equivalents but carry a scale factor (for example, `cm → [1, 0, 0, 0, 0, 0, 0]` with scale `10⁻²`); the scale factor is folded into literal values during type checking and does not appear at runtime.

Dimension equality is structural array equality, which makes type comparison cheap. The compiler does not attempt to display dimensions in their user-supplied form; error messages produced by `format_si` always show the canonical SI base form (`kg·m·s⁻²` rather than `N`), which loses some readability but avoids the complexity of a unit-system-aware formatter.

### Type checker algorithm

The checker is bidirectional in the sense of [Pierce and Turner, "Local Type Inference"]. It walks the AST in two modes:

- **Synthesis** (bottom-up): given an expression, compute its type from its parts. Used for literals, identifiers, applications of fully-typed functions, and most binary operations.
- **Checking** (top-down): given an expression and an expected type, verify that the expression has that type. Used at `let` bindings, function returns, function-call arguments, and the right-hand side of any annotated context.

A small unification table handles the two cases where bidirectional checking alone is insufficient: enum constructor calls (where the type arguments must be inferred from value arguments), and `match` arms (where all arms must produce the same type, even when the first arm's type contains type variables that other arms refine).

Unification is restricted: there is no let-generalization, no occurrence check beyond the trivial (we forbid `Var(α) ≡ ... Var(α) ...`), and no row polymorphism. The implementation is a union-find table (`Vec<Option<Ty>>` indexed by `TypeVarId`). When the checker finishes a function body, all `Var`s introduced within that function are required to be resolved; an unresolved `Var` is reported.

For most spec rules, the bidirectional formulation is straightforward. The interesting cases:

- **Implicit `Int → Scalar` conversion.** When the checking mode expects `Scalar(d)` and the synthesized type is `Int`, the checker accepts the conversion only if `d == Dimension::ZERO`. The conversion does not synthesize: an `Int` literal in synthesis mode produces `Ty::Int`, never `Ty::Scalar`.

- **Operator dimension propagation.** Multiplication and division compute the result dimension from operand dimensions. Addition and subtraction require operand dimensions to be equal and produce the shared dimension. Powers require the exponent to be a compile-time integer (an `IntLit` expression); a non-literal exponent is a type error in 3d.

- **Vector and matrix shape rules.** `Vec<N> + Vec<M>` requires `N == M`. `Mat<M, N> * Vec<N>` produces `Vec<M>`. `Mat<M, N> * Mat<N, P>` produces `Mat<M, P>`. Shape mismatches are reported.

- **Match arm unification.** All arms' body types must unify. The first arm's type seeds the expected type; subsequent arms are checked against it (or unified if it contains `Var`s).

- **Enum constructor inference.** `Some(x)` where `x: Int` produces `Option<Int>` because `Some(T)` requires the type variable `T` to unify with the type of `x`.

The full bidirectional rule set is to be specified in PR-3b's plan and implemented incrementally; the rules listed here document the key non-obvious cases that constrain the design.

### Module structure

The new code lives in `compiler/src/sema.rs` (entry point) and the `compiler/src/sema/` subdirectory. The directory grows over the course of the five PRs:

- `sema.rs` — entry point. Defines `TypedProgram` and `pub fn check(prog: Program) -> Result<TypedProgram, Vec<Diagnostic>>`.
- `sema/ty.rs` — `Ty`, `Dimension`, `TypeVarId`, `NodeId`, `DefId`, and the AST `Type → Ty` conversion routine. Added in 3a.
- `sema/resolve.rs` — name resolution, `SymbolTable`, and the resolution table. Added in 3a.
- `sema/diag.rs` — sema-specific diagnostic helpers (constructors for common error shapes). Added in 3a.
- `sema/check.rs` — bidirectional type checker. Added in 3b.
- `sema/unify.rs` — unification table. Added in 3b.
- `sema/exhaust.rs` — match exhaustiveness. Added in 3c.
- `sema/precision.rs` — spec §6.1 precision warning analysis. Added in 3e.

The `mod.rs` convention is not used; the project follows the Rust 2024 edition `foo.rs + foo/` layout established in the existing `parser.rs + parser/` and `ast.rs + ast/` modules.

### Error model

The existing `compiler/src/error.rs` is renamed to `compiler/src/diag.rs`, and `CompileError` becomes `Diagnostic`. The struct gains four fields: a `Level` enum (`Error`, `Warning`, `Note`), the existing `kind` is renamed `phase` (`Lex`, `Parse`, `Sema`), and two collections — `labels: Vec<(Span, String)>` for secondary spans with annotations, and `notes: Vec<String>` for free-form follow-up text:

```rust
pub struct Diagnostic {
    pub level: Level,
    pub phase: Phase,
    pub span: Span,
    pub message: String,
    pub labels: Vec<(Span, String)>,
    pub notes: Vec<String>,
}
```

Existing constructors (`CompileError::lex`, `CompileError::parse`) are preserved as `Diagnostic::lex_error`, `Diagnostic::parse_error`. New constructors (`Diagnostic::type_error`, `Diagnostic::warning`) are added for sema use. A builder pattern (`with_label`, `with_note`) lets callers attach secondary information without bloating the constructor signature.

The richer fields exist to support type-checker error messages of the form "expected `Scalar<kg>` here, found `Scalar<m>` here" with two labelled spans, and "did you mean `to_int(x)`?" notes. Spec §6.1 precision warnings are represented at `Level::Warning`.

### Symbol table

Name resolution is implemented in 3a with a simple lexically scoped symbol table. Scopes form a stack: entering a function or a block pushes a scope, exiting pops it. Top-level definitions populate the root scope. Lookup walks the stack from innermost to outermost.

The exact API and scope-entry rules are settled in 3a's plan. The constraints from this Design Doc are:

- Top-level definitions are hoisted: forward references between top-level functions are permitted.
- Function parameters and the function body share a scope.
- `let` bindings introduce a new name in the current scope; shadowing within the same scope is rejected (matching the spec's lack of an explicit shadowing rule).
- Closures capture by reference; captured names must resolve at the closure-definition site (no late binding).

### Standard library type signatures

Standard library functions described in spec §7 are declared as built-in `DefId`s during checker initialization. The exact signatures are settled in 3e's plan; the constraints are:

- `printf(format: String, ...) -> ()` — variadic. Variadic support requires either a special-case rule in the call-checker or a sentinel `Ty` variant; the choice is settled in 3e.
- `panic(message: String) -> !` — diverges. The `Ty::Never` (or equivalent) is added in 3e if not earlier.
- `to_int(x: Scalar) -> Int` — only accepts dimensionless `Scalar`.
- `kahan_sum(xs: Array<Scalar<U>>) -> Scalar<U>` — generic over the unit `U`. Because user-defined generic functions are a non-goal, this signature is encoded as a built-in special form rather than a regular function declaration.
- File I/O signatures (`open`, `read`, `write`, `close`) return `Result<File, Error>` per spec §7.7.

The built-in symbol-table population happens at the start of `sema::check`, before user-program resolution.

### Precision warning detection (spec §6.1)

The compiler emits a warning when a floating-point summation pattern in a loop body risks rounding-error accumulation. The exact detection rules are settled in 3e's plan. The contract is:

- The analysis runs after type checking, on the `TypedProgram`.
- It detects expressions of the form `accumulator = accumulator + x` (or `+=` if the language adds it later) inside `for` or `while` bodies, where `accumulator` and `x` are both `Scalar` (with any unit).
- A warning is emitted suggesting `kahan_sum` or another compensated-summation strategy. The warning's primary span is the addition expression; a label points to the accumulator's binding site.

The analysis is conservative: it warns on patterns that look like accumulation but does not attempt to prove the sum is unsafe (which would require a numerical analysis). False positives are acceptable; false negatives are also acceptable but should be minimized.

## Cross-cutting Concerns

### Backward compatibility

The 0-th PR (Diagnostic rename) renames the public type `CompileError` to `Diagnostic`. Any external consumer that imports `CompileError` from `dyne_compiler` (currently none, since dyne is not yet published) would break. This is acceptable because Stage 3 is pre-1.0 and no stability commitment exists.

NodeId addition to the AST is a backward-incompatible change to AST construction sites in the parser, but the public API of `compile()` is preserved.

### Testing strategy

Each slice extends the test suite. The conventions are:

- **Unit tests** for `sema/ty.rs` (Dimension arithmetic, Ty equality, AST `Type → Ty` conversion) and `sema/unify.rs` (unification table behaviour).
- **Integration tests** in `compiler/tests/end_to_end.rs` (or a sibling `sema_e2e.rs`) that run `check()` on small dyne programs and assert success or specific diagnostics.
- **Sample programs** in `samples/` exercising every Stage 3 feature, verified by the existing `compiler/tests/samples.rs` harness.
- **Diagnostic snapshot tests** for error messages that need to be locked down (using simple substring assertions per the project's existing convention, not full-output snapshot frameworks).

Each PR's plan specifies its expected baseline test count and the count after the PR lands.

### Performance

The type checker is not on a hot path during program execution, but compilation speed is a user-facing concern. The choices here are budgeted for simplicity over speed:

- Dimension equality is array compare (cheap).
- Type table lookups are `HashMap<NodeId, Ty>` (O(1) average; for compilation units of a few thousand nodes this is acceptable).
- Unification uses a `Vec<Option<Ty>>` rather than a path-compressed union-find. A future optimization can switch to union-find if profiling shows unification is a bottleneck.

### Diagnostic UX

The Diagnostic type's two new collections (`labels`, `notes`) are not yet rendered by the existing `Diagnostic::render` method. PR-0 adds them as data fields without changing rendering; PR-3e implements multi-span rendering. Until then, only the primary span and message are displayed, matching the current behaviour.

## Alternatives

### AST integration: annotated AST vs. side-table vs. mirror tree

Three alternatives were considered for storing type information.

The **annotated AST** alternative adds a `pub ty: Option<Ty>` field directly to `Expr`. The parser leaves it `None`; the checker fills it in. This is what Go's `gc` compiler and Swift's compiler do. It is the cheapest to implement (one field, no `NodeId` infrastructure, no `HashMap`) and is well-suited to small compilers. It was rejected because the AST gains a "pre-checking" and "post-checking" dual state — `expr.ty.unwrap()` calls scatter through the codebase, and the parser's output is no longer a pure snapshot. For multiple independent annotation passes (precision warnings, future analyses) the dual state compounds: each new field adds to every `Expr` whether or not the pass applied to that node.

The **mirror typed-AST** alternative builds a separate `TypedExpr` enum that mirrors `ExprKind` with each variant carrying explicit type information. This is what OCaml does. It is the cleanest in terms of phase-boundary type safety (the codegen can take `&TypedExpr` and Rust enforces that it was type-checked) but pays a high cost: a parallel enum that must be maintained alongside the AST, plus an explicit `Expr → TypedExpr` conversion. For dyne's current scale (the AST has roughly 50 variants across `Expr`, `Stmt`, `Type`, `Pattern`, and `Item`), the mirror duplication is significant.

The chosen **side-table with NodeId** approach is what rustc uses (`HirId → Ty` via `TypeckResults`). It keeps the AST as a snapshot, allows multiple orthogonal annotation tables, and supports phase-boundary type safety via the `TypedProgram` wrapper struct. The cost is the `NodeId` infrastructure (one field on every span-bearing node, plus a parser counter). For dyne's anticipated trajectory (multiple analysis passes, possible future MIR), this trade-off favours the side-table.

### Type checker algorithm: pure bidirectional vs. HM vs. HM-lite

A pure **bidirectional** checker (option X in the discussion) is the simplest formulation that satisfies the spec, since all bindings, parameters, and returns are annotated. It was rejected because enum constructor inference (`Some(x)` instantiating `T` from `x`'s type) and `match` arm unification both require some form of constraint solving. Implementing these as ad-hoc local inference works but is fragile when arms have type variables that interact across multiple arms.

A **full Hindley-Milner** checker (option Y) handles all the cases the bidirectional approach does, and additionally supports user-defined generic functions through let-generalization. It was rejected because dyne does not have user-defined generic functions (the spec's only generics are enum type parameters), and HM's let-generalization machinery (env-based polymorphic vs. monomorphic distinction, generalization at let boundaries, instantiation at use sites) is significant complexity for no current benefit. If user-defined generic functions are added, the migration is well-defined: add a generalization phase to the existing unification machinery.

The chosen **HM-lite** approach (option Z) is bidirectional checking augmented with a small unification table. It does not support let-generalization but uses unification for enum instantiation and match arm joining. The forward-compatibility path to full HM is preserved.

### Unit representation: dimension vector vs. symbolic tree vs. unit-name map

A **symbolic tree** representation (option β in the discussion) keeps units as the same tree the parser produces (`UnitExpr::Atom("kg")`, `UnitExpr::Mul(...)`, etc.). It was rejected because equivalence becomes structural equality after normalization; `kg·m` and `m·kg` need to be recognized as the same, requiring associativity, commutativity, and exponent-collection rewrite rules. The integer dimension vector achieves the same equivalence as a single array compare.

A **unit-name keyed map** (option γ, `Map<String, i32>` from unit name to exponent) is an intermediate position. It avoids the tree's normalization complexity but requires unit names to be canonicalized (`m` is base, `km` is prefixed; `N` and `kg·m·s⁻²` must hash to the same key). The integer dimension vector sidesteps this by reducing every unit name to its base-dimension contribution at the parsing-to-checker boundary.

A **rational-exponent vector** (option δ) generalizes the integer vector to support fractional exponents (`Hz^(1/2)` for noise spectra). It was rejected for the initial implementation because integer exponents cover dyne's intended physics domain (Hamiltonian mechanics, symplectic integration). Future migration to rational exponents replaces `i8` with a `Rational` type internally and changes the `pow` argument from `i32` to `Rational`; the rest of the API and all callers are unchanged.

### Module structure: single `sema/` vs. phase-split

A **phase-split** module structure (separate `compiler/src/resolve/` for name resolution, `compiler/src/typecheck/` for type checking, etc.) follows rustc's pattern (`rustc_resolve`, `rustc_hir_typeck`, `rustc_borrowck`). It was rejected because rustc's split is justified by team-scale concerns — different teams own different phases — that do not apply to dyne. A single `sema/` module with several files keeps the responsibility separation visible at the file level without imposing the overhead of separate top-level crates.

### Error model: extend in place vs. new type vs. rename + extend

Extending `CompileError` in place (option A) was rejected because the type's name is misleading once it carries warnings: a `CompileError::warning` is contradictory. Introducing a separate `SemaError` type for the new phase (option B) was rejected because the unified output displayed to the user must come from a single type, and a per-phase error type that converts at the boundary doubles the maintenance surface. Renaming `CompileError` to `Diagnostic` and extending in place (option C, chosen) is a one-time refactor that yields a clean unified type for all phases. The rename is mechanical (roughly 30 sites) and lands as PR-0 before any new feature work.
