# Language Specification: Dyne

## 1. Overview

Dyne is a compiled programming language specialized for scientific computing. The name comes from the cgs unit of force — fitting for a language whose type system carries physical units. This specification defines the syntax, type system, and semantics of the language. Source files use the `.dy` extension.

## 2. Lexical Structure

### 2.1 Comments

Everything from `//` to the end of the line is treated as a comment. Multi-line comments are not supported.

```
// This is a comment
let x: Scalar = 1.0 // Inline comment
```

### 2.2 Literals

#### Numeric Literals

Integer literals and floating-point literals are distinguished. Floating-point literals contain a decimal point.

```
42        // Integer literal
3.14      // Floating-point literal
1.0e-10   // Exponential notation
```

#### String Literals

Enclosed in double quotes.

```
"Hello, World"
```

#### Vector Literals

Elements are separated by commas within square brackets. Newlines inside the brackets are ignored, and a trailing comma is allowed.

```
[1.0, 2.0, 3.0]

[
  1.0,
  2.0,
  3.0,
]
```

#### Matrix Literals

Nested vector literals. As with vectors, newlines inside the brackets are ignored and a trailing comma is allowed.

```
[[1.0, 0.0], [0.0, 1.0]]

[
  [1.0, 0.0, 0.0],
  [0.0, 1.0, 0.0],
  [0.0, 0.0, 1.0],
]
```

### 2.3 Operators

#### Arithmetic Operators

`+` (addition), `-` (subtraction), `*` (multiplication), `/` (division), `^` (exponentiation)

#### Comparison Operators

`==`, `!=`, `<`, `>`, `<=`, `>=`

#### Logical Operators

`and`, `or`, `not`

## 3. Syntax

### 3.1 Variable Definition

Variables are defined using the `let` keyword. Type annotations are required. Reassignment is allowed.

```
let x: Scalar = 1.0
x = 2.0  // Reassignment
```

### 3.2 Function Definition

Defined using the `function` keyword and closed with `end`. Type annotations are required for parameters and return values. Return values must be explicit using `return`.

```
function add(a: Scalar, b: Scalar): Scalar
    return a + b
end
```

### 3.3 Anonymous Functions

For single-expression functions, the expression follows `->`. For multi-line functions, a newline follows `->` and the body is closed with `end`.

```
// Single-line
let square: Fn(Scalar) -> Scalar = (x) -> x ^ 2

// Multi-line
let compute: Fn(Vec<3>) -> Scalar = (q) ->
    let a = dot(q, q)
    return a + 1.0
end
```

### 3.4 Control Flow

#### Conditional

```
if x > 0 then
    ...
elseif x == 0 then
    ...
else
    ...
end
```

#### For Loop

Two forms are provided: range loop and iteration loop. The range loop is exclusive of the upper bound.

```
// Range loop (iterates 0, 1, 2. 3 is excluded)
for i = 0, 3 do
    ...
end

// Iteration loop
for x in arr do
    ...
end

// Dictionary iteration
for key, value in params do
    ...
end
```

#### While Loop

```
while x > 0 do
    ...
end
```

### 3.5 Struct

Structs hold data only and do not have methods.

```
struct State
    q: Vec<3>
    p: Vec<3>
    t: Scalar
end

let s = State { q: [1.0, 0.0, 0.0], p: [0.0, 1.0, 0.0], t: 0.0 }
```

### 3.6 Module

Modules are loaded per file using `import`.

```
import math
import simulation.integrator
```

### 3.7 Array Operations

Element access uses 0-based indexing. Insertion, removal, and length are provided as functions.

```
let arr: Array<Scalar> = [1.0, 2.0, 3.0]
let x: Scalar = arr[0]       // Element access
push(arr, 4.0)               // Append to end
let y: Scalar = pop(arr)     // Remove from end
let len: Int = length(arr)   // Length
```

### 3.8 Dictionary Operations

Values are accessed, added, updated, and removed by key.

```
let params: Dict<String, Scalar> = {"mass": 1.0, "k": 0.5}
let m: Scalar = params["mass"]        // Access
params["damping"] = 0.1               // Add / Update
let has: Bool = contains(params, "k") // Check key existence
remove(params, "damping")             // Remove
```

## 4. Type System

### 4.1 Primitive Types

| Type | Description |
|---|---|
| `Scalar` | 64-bit floating-point number (f64) |
| `Int` | 64-bit signed integer (i64) |
| `String` | String |
| `Bool` | Boolean |

### 4.2 Collection Types

| Type | Description |
|---|---|
| `Vec<N>` | N-dimensional vector |
| `Mat<M, N>` | M-by-N matrix |
| `Array<T>` | Variable-length array |
| `Dict<K, V>` | Dictionary |

### 4.3 Function Type

```
Fn(ParamType, ...) -> ReturnType
```

### 4.4 Unit-Annotated Types

Units can be attached as the last type parameter. Units are optional; omitting them means the value is dimensionless.

```
let mass: Scalar<kg> = 1.5
let velocity: Vec<3, m/s> = [1.0, 2.0, 3.0]
let m: Mat<2, 2> = [[1.0, 0.0], [0.0, 1.0]]  // Matrices are dimensionless
```

Unit consistency is checked at compile time. Inconsistencies result in a compile error.

### 4.5 Unit Systems

The initial release provides SI, CGS, and Gaussian unit systems as built-ins. User-defined unit systems will be supported in the future.

### 4.6 Sum Types and Pattern Matching

Sum types (tagged unions) are defined using the `enum` keyword. `Result` and `Option` are provided as built-in sum types.

```
enum Result<T, E>
    Ok(T)
    Err(E)
end

enum Option<T>
    Some(T)
    None
end
```

User-defined sum types can also be declared:

```
enum Energy
    Kinetic(Scalar)
    Potential(Scalar)
    Total(Scalar, Scalar)
end
```

Pattern matching is performed using `match`. Each arm starts with `case Pattern then body`. Pattern forms include wildcards (`_`), bindings, variants with payload, and integer / boolean / string literals. Floating-point literal patterns are rejected at compile time because IEEE 754 equality is unreliable (NaN ≠ NaN, rounding error).

```
let file: Result<File, Error> = open("data.csv", "r")
match file
    case Ok(f) then
        // use f
    case Err(e) then
        printf("Error: %s\n", e)
end
```

Pattern matching must be exhaustive. If any variant is not covered, a compile error is raised.

```
// Compile error: missing case `None`
match opt
    case Some(x) then
        ...
end
```

### 4.7 Type Conversion

Implicit conversion from `Int` to a dimensionless `Scalar` happens for integer literals and for `Int` operands inside arithmetic expressions (e.g. `i * dt`); a bare `Int` variable is not implicitly converted on direct assignment. In an expected-type context where the destination is a unit-annotated `Scalar<u>` or `Vec<n, u>` (let-binding with annotation, function parameter, function return type, or struct-field initializer), a dimensionless **numeric literal** of the matching shape (an integer or float literal — including a negated literal — typed as a unit-less `Scalar`, or a unit-less `Vec<n>` literal) is implicitly promoted to the annotated unit; the destination annotation determines the unit unambiguously. A dimensionless **variable or computed expression** is *not* promoted in these contexts — promoting it would risk silently mislabeling a count or ratio as a physical quantity (e.g. turning a loop counter into a mass) — so it must be handled explicitly. Outside expected-type contexts (e.g. a bare subexpression with no expected type, such as `1.5 + mass`), assignment of a dimensionless value to a unit-annotated `Scalar` remains a type error. Conversion from `Scalar` to `Int` requires an explicit conversion function.

```
let i: Int = 3
let x: Scalar = i              // Compile error: a bare Int variable is not implicitly converted on assignment
let count: Scalar = 3          // OK: an integer literal widens to a dimensionless Scalar
let mass: Scalar<kg> = i       // Compile error: a dimensionless variable is not implicitly unit-annotated
let g: Scalar<m/s^2> = 9.8     // OK: a numeric literal coerces to the annotated unit
let dt: Scalar<s> = 0.01       // OK: literal
let t: Scalar<s> = i * dt      // OK: i -> Scalar (dimensionless) inside the expression; unit propagated by *
let n: Int = to_int(count)     // Explicit conversion required
```

### 4.8 Vector/Matrix Dimension Checking

Dimensional consistency of vector and matrix operations is checked at compile time.

```
let a: Vec<3> = [1.0, 2.0, 3.0]
let b: Vec<2> = [1.0, 2.0]
let c = a + b  // Compile error: cannot add Vec<3> and Vec<2>

let m: Mat<2, 3> = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]]
let v: Vec<3> = [1.0, 2.0, 3.0]
let result: Vec<2> = m * v  // OK: Mat<2,3> * Vec<3> -> Vec<2>
```

## 5. Error Handling

### 5.1 Unrecoverable Errors

Unrecoverable errors are triggered by the built-in `panic` function, immediately terminating the program. The runtime prints the error message and a stack trace showing the call chain leading to the panic.

```
if mass < 0.0 then
    panic("mass must be non-negative")
end
```

Output:

```
panic: mass must be non-negative
  at simulation.dy:12
  at main:45
```

### 5.2 NaN/Infinity

By default, NaN and infinity propagate in accordance with IEEE 754. A compiler option allows switching to panic on NaN/infinity generation.

### 5.3 Recoverable Errors

Errors at external boundaries (e.g., file I/O) are handled using sum types (`Result`/`Option`). See section 4.6 for syntax details.

## 6. Compiler Features

### 6.1 Compile-Time Precision Warnings

The compiler statically analyzes floating-point addition patterns within loops and warns when there is a risk of rounding error accumulation.

### 6.2 Compile-Time Dimension Checking

The compiler checks dimensional consistency of unit-annotated types at compile time.

## 7. Standard Library (Overview)

### 7.1 Automatic Differentiation

Provides partial differentiation for arbitrary scalar functions. Can be used to automatically derive Hamilton's canonical equations of motion.

### 7.2 Symplectic Integrators

Provides symplectic Euler method, Stormer-Verlet method, and 4th-order symplectic integration.

### 7.3 Compensated Summation

The `kahan_sum` function suppresses rounding error accumulation in floating-point addition.

### 7.4 Physical Constants

Provides fundamental physical constants (speed of light, Planck constant, Boltzmann constant, gravitational constant, etc.) as unit-annotated values.

### 7.5 Nondimensionalization

Provides functionality to transform equations into dimensionless form by specifying characteristic scales.

### 7.6 Input/Output

Provides formatted output via the `printf` function.

```
printf("Energy: %f at t=%f\n", energy, t)
```

### 7.7 File I/O

Provides basic file operations: opening, reading, writing, and closing files. File operations return `Result` types for error handling.

```
let file: Result<File, Error> = open("output.csv", "w")
match file
    case Ok(f) then
        write(f, "t,energy\n")
        write(f, printf("%f,%f\n", t, energy))
        close(f)
    case Err(e) then
        printf("Failed to open file: %s\n", e)
end
```

## 8. Semantics

### 8.1 Evaluation Strategy

Strict evaluation is adopted. All function arguments are evaluated before the function body is executed.

### 8.2 Scope

Block scoping is adopted. Variables defined within `function`, `if`, `for`, and `while` blocks are only accessible within that block.

### 8.3 Closures

Anonymous functions can reference variables from the enclosing scope at the point of definition.

```
let k: Scalar = 0.5
let force: Fn(Vec<3>) -> Vec<3> = (q) -> -k * q  // References k
```

### 8.4 Argument Passing

All arguments behave as pass-by-value (copy). The compiler may internally optimize copies (e.g., copy-on-write).
