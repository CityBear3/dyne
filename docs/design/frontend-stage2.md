# Design Doc: Dyne Compiler Frontend, Stage 2

| Field | Value |
|---|---|
| Status | Draft |
| Author | CityBear3 (design ownership) / Claude Code (drafter by delegation) |
| Created | 2026-04-27 |
| Scope | Parser support for `struct`, `enum`, and `match` (Stage 2 of the frontend) |
| Prerequisites | `docs/language-spec.md`, `docs/design/frontend.md` (Stage 1) |

## 1. Overview

Stage 2 extends the parser implemented in Stage 1 to recognize the remaining language constructs in `language-spec.md` §3.5 and §4.6: structure definitions and their literal form, sum-type definitions with generic parameters, and pattern-matching expressions. The AST already carries the corresponding nodes (defined in Stage 1 for forward-compatibility), so Stage 2 is primarily a parser-side effort, with a small extension to the pattern AST and a single new keyword in the lexer.

The work also includes one spec amendment: match arms are introduced with an explicit `case` keyword. The original spec used `Pattern then body` with no arm-starter token, which forces speculative pattern parsing during arm-body consumption. Adding `case` makes arm boundaries detectable with a single-token lookahead, simplifies the parser, and improves error messages near arm boundaries.

## 2. Context

Stage 1 delivered a working frontend for the imperative core of the language: type annotations (including units), `let` bindings, function definitions, expressions, and control flow. The remaining gap before the language can express the data-model-driven examples in the spec is the absence of nominal types (`struct`, `enum`) and the discrimination machinery (`match`) that goes with them.

Stage 1 also pre-defined the Stage 2 AST nodes — `StructDef`, `StructField`, `EnumDef`, `EnumVariant`, `Pattern`, `MatchArm`, `ExprKind::StructLit`, and `ExprKind::Match` — to avoid AST churn when Stage 2 lands. That choice is now paying off: this design adds three pattern variants (`IntLit`, `BoolLit`, `StrLit`) and otherwise leaves the AST untouched.

## 3. Goals and Non-Goals

### Goals

- Parse `struct` definitions and their associated literal-construction expressions.
- Parse `enum` definitions, including generic type parameters such as `Result<T, E>`.
- Parse `match` expressions with arms introduced by a new `case` keyword.
- Parse the pattern forms required by `match`: wildcard `_`, identifier binding, variant with payload, integer literal, boolean literal, and string literal. Support a unary minus prefix on integer literals.
- Reject floating-point literal patterns at parser time with an educational error.
- Apply the multi-line and trailing-comma conventions established in Stage 1 (Vec/Mat literals, function signatures) to the new constructs where structurally analogous.

### Non-Goals

- Type checking, exhaustiveness checking, and unification of pattern types against the scrutinee. These belong to a later semantic-analysis design.
- Struct-destructuring patterns (`State { q, p, t }` inside `match`). The AST does not currently model field-named patterns; adding them is deferred to a later PR.
- Range patterns (`0..=10`) and or-patterns (`Some(1) | Some(2)`). Both are common in mature pattern matchers but require additional AST and syntactic surface; deferred.
- Module / import parsing (Stage 4 in the original frontend roadmap).
- Lambda expressions (Stage 3 in the original frontend roadmap).

## 4. Detailed Design

### 4.1 Spec Amendment: `case` Keyword in Match Arms

The original spec (§4.6) introduced match arms as `Pattern then body`. With no arm-starter token, the parser cannot tell whether the next line continues the previous arm's body or starts a new arm without speculatively parsing a pattern and looking for `then`. Speculation undermines error messages: a typo in an arm body that happens to look pattern-shaped may be silently absorbed as the start of the next arm, and the resulting error is reported far from the actual mistake.

The amendment introduces `case` as the arm-starter:

```
match file
    case Ok(f) then
        // use f
    case Err(e) then
        printf("Error: %s\n", e)
end
```

This makes every arm visually scannable and reduces arm-boundary detection to a single-token check (`Case` or `End`). It also aligns Dyne's match form with the family of pattern-matching languages that use a keyword arm-starter (Scala, Swift, Erlang/Elixir, Python 3.10+).

The amendment is small. `language-spec.md` §4.6 needs the new keyword called out, and the example block updated. No other section refers to the old form.

### 4.2 Struct Definition

A struct definition is a top-level item with the form

```
struct Name
    field_name: Type
    field_name: Type
    ...
end
```

Field declarations follow Stage 1's general rule: each statement (here, each field) is terminated by a Newline, Eof, or block-terminator. The newline terminator means commas between fields are not required. For consistency with the multi-line and trailing-comma conventions used in `Vec`/`Mat` literals and (after PR #6) function signatures, an optional trailing comma is accepted on each field as well, although it is unnecessary when newlines are used.

The parser is added to `parse_item` as a third top-level form (in addition to `function` and `let`). The body is a flat list of fields, parsed by reusing `parse_param`-style logic since `name: Type` has the same shape there.

Struct definitions do not carry generic parameters in this stage. The spec example `struct State` is monomorphic, and Dyne's stdlib roadmap does not yet require generic structs. If they become necessary later, the AST already has room (via a `Vec<String>` field analogous to `EnumDef::type_params`) and the parser can be extended.

Field declarations are written on a single line (`name: Type`); inline newlines between the name, colon, and type are not permitted. This is consistent with Stage 1's `let` and function-parameter conventions, which also reject newlines internal to a `name: Type` construct. Newlines between fields, and an optional trailing comma per field, are accepted (see §5.1).

### 4.3 Struct Literal Expression

A struct literal has the form

```
StructName { field_name: expr, field_name: expr, ... }
```

It is an expression-position construct, not a statement, and is added to `parse_postfix` as a new postfix that fires when the current expression is a plain `Ident` followed by `{`. Other postfix forms (call, index, field access) take precedence in their own contexts since they begin with `(`, `[`, or `.` respectively, so there is no ambiguity within `parse_postfix` itself.

A potential ambiguity exists between an `Ident { ... }` struct literal and the `{`/`}` token pair as it could appear elsewhere, but Dyne's other syntactic constructs do not currently use braces, so the brace immediately after an identifier in expression position can only be a struct literal.

Inside the braces, the parser accepts newlines around field assignments and a trailing comma after the last field, mirroring `Vec`/`Mat` literals. The shape of each field assignment is `Ident COLON expr`. Field order in the literal is preserved in the AST as a `Vec<(String, Expr)>`; semantic-phase ordering and missing-field detection are out of scope here.

### 4.4 Enum Definition

An enum definition is a top-level item with the form

```
enum Name<TypeParam, ...>
    Variant
    Variant(PayloadType, ...)
    ...
end
```

The optional `<TypeParam, ...>` block introduces zero or more type parameters as bare identifiers. These names are not types in the surrounding scope; they are bindings introduced by the enum and referenced by variant payload types. The AST stores them as `Vec<String>`.

Variant declarations come in two shapes: a bare name (no payload, e.g. `None`) or a name followed by a parenthesized list of payload types (`Ok(T)`, `Total(Scalar, Scalar)`). Each variant is on its own line; commas separate payload types within the parens but not variants between each other. As with struct fields, multi-line and trailing-comma support carry over to the variant payload list for consistency with function signatures.

Type parameters from the enum header are visible inside the variant payload types. The Stage 1 type parser already accepts bare identifiers as `TypeKind::Named(...)`, so no special handling is needed: `Ok(T)` parses as `EnumVariant { name: "Ok", payload: [Type::Named("T")] }`. Resolution of `T` to the introducing parameter is a semantic-phase concern.

### 4.5 Match Expression

A match expression has the form

```
match scrutinee
    case Pattern then body
    case Pattern then body
    ...
end
```

`match` is added to `parse_primary` next to `if` since both produce expressions and start with a distinguishing keyword. The scrutinee is a full expression. After parsing the scrutinee and consuming any newlines, the parser enters an arm loop that terminates when it sees `End`. Each arm consumes `case`, then a pattern, then `then`, then an arm body. The arm body is a `Block` and is parsed by reading statements until the next token is `End` or `Case`.

Reusing `parse_block_until` from Stage 1 is attractive but its terminator interface accepts only the existing `Else`/`Elseif`/`End` markers used by `if`. Rather than overloading that helper with another marker, this design adds a small dedicated `parse_match_arm_body` that uses `End`/`Case` as the boundary. The two helpers share the same loop shape — consume newlines, check for terminator, parse a statement, require statement terminator, repeat — so the duplication is small and the call sites stay readable.

Each arm body is a full block (a sequence of statements), not a single expression. This is consistent with the AST (`MatchArm.body: Block`) and with the spec example, which shows multi-statement arm bodies. The block-as-expression value of the body is a semantic-phase concern; the parser only ensures the syntactic shape.

A match expression with zero arms is a parse error: `match x\nend` is rejected with a message indicating that at least one `case` arm is required. This is a parser-level decision rather than a semantic-phase exhaustiveness check because it is also syntactically meaningless.

### 4.6 Pattern Parsing

The pattern grammar accepted in Stage 2 is

```
Pattern := '_'                              -- wildcard
         | Ident                            -- binding (or no-payload variant; resolved in semantic phase)
         | Ident '(' Pattern (',' Pattern)* ','? ')'   -- variant with payload
         | IntLit | '-' IntLit              -- integer literal (with optional unary minus)
         | true | false                     -- boolean literal
         | StrLit                           -- string literal
```

Wildcard `_` is handled by recognizing the identifier `"_"` as a special case at the start of `parse_pattern` and emitting `PatternKind::Wildcard`. The lexer already tokenizes `_` as `Ident("_")`, so the lexer is unchanged.

For an `Ident` token, the parser looks ahead: if the next token is `LParen`, the pattern is `Variant(name, payload_patterns)`; otherwise it is `Ident(name)`. Distinguishing a no-payload variant such as `None` from a variable binding is left to the semantic phase, since both forms produce `PatternKind::Ident` at parse time. The semantic phase can disambiguate with type information.

Integer literal patterns are parsed directly from `Int(_)` tokens. A leading `-` followed by `Int(_)` produces a negated integer pattern, parsed as a small two-token sequence specific to pattern position. This is not full prefix-operator support — only `-` followed by an integer literal is recognized — because patterns are not arbitrary expressions and need not admit the full Pratt machinery.

Boolean literal patterns come from the `True` and `False` keyword tokens. String literal patterns come from `Str(_)`. Both pass through with no additional logic.

Floating-point patterns are explicitly rejected. When the parser sees a `Float(_)` token in pattern position, it emits a parse error with an explanation: `floating-point literal patterns are not supported because NaN ≠ NaN and rounding error makes equality matches unreliable; use a guard such as 'if abs(x - 0.5) < eps' instead`. This is documented in §5 (Cross-cutting concerns) below as a deliberate design decision rather than a limitation to fix later.

### 4.7 AST Extensions

The only AST change is to extend `PatternKind` (defined in `compiler/src/ast/item.rs`) with three literal variants:

```rust
pub enum PatternKind {
    Wildcard,
    Ident(String),
    Variant(String, Vec<Pattern>),
    IntLit(i64),     // new
    BoolLit(bool),   // new
    StrLit(String),  // new
}
```

The variants mirror the corresponding `ExprKind` literal forms. There is no `FloatLit` variant: by rejecting float literal patterns at parser time, the AST is not exposed to a value class that the language has chosen not to support.

No other AST type changes. `MatchArm.body: Block` already supports multi-statement arm bodies. `ExprKind::StructLit(String, Vec<(String, Expr)>)` and `ExprKind::Match(Box<Expr>, Vec<MatchArm>)` are unchanged.

### 4.8 Lexer Extensions

The lexer adds one keyword: `Case`. The keyword table in `TokenKind::keyword` gains a single entry mapping `"case"` to `TokenKind::Case`. No new operator or delimiter tokens are required; struct literals, enum variant payloads, and match arm bodies all reuse `LBrace`/`RBrace`, `LParen`/`RParen`, `Comma`, `Colon`, and `Newline`.

## 5. Cross-cutting Concerns

### 5.1 Multi-line and Trailing-comma Conventions

Stage 1 established a uniform treatment of newlines and trailing commas inside delimited list constructs: `[ ... ]` for vectors and matrices, and `( ... )` for function signatures and calls. Stage 2 extends the same treatment to struct definitions (between fields), enum definitions (within a variant's payload), struct literals (between field assignments), and variant payload patterns. The implementation pattern is the same — `consume_newlines` after the opening delimiter, after each item, and after each comma; break out of the parse loop after consuming a comma if the next token is the closing delimiter.

Match arm separators do not need this treatment because the boundary between arms is indicated by the `case` keyword rather than punctuation.

### 5.2 Floating-point Pattern Rejection

Allowing `case 0.5 then ...` would be a misuse trap in a language whose arithmetic propagates IEEE 754 semantics. `0.1 + 0.2 == 0.3` evaluates to false; `NaN == NaN` evaluates to false; subtle precision differences from compiler optimizations could cause matches to silently change. Other languages with similar concerns have either deprecated float patterns (Rust) or warned against their idiomatic use (OCaml, Haskell). Dyne, as a physics-computational language, takes the strictest position and rejects them at parse time.

The error message is intentionally educational: it names the specific causes (NaN, rounding), suggests the correct alternative (an `if` guard with an epsilon comparison), and points readers toward the safe pattern. The same logic applies to negative floats: the parser rejects `Minus Float` sequences in pattern position.

### 5.3 Error Message Quality at Arm Boundaries

The `case` amendment is partly an error-quality decision. With speculative pattern parsing, a typo that produces a partially-parseable pattern would either be absorbed into the previous arm's body (with the resulting error reported at the wrong location) or cause the parser to commit and then fail when `then` is missing. With `case` as the arm-starter, the parser commits to "this is a new arm" the moment it sees the keyword; subsequent errors inside the pattern are reported at the actual position of the offending token, matching the experience users have come to expect from Stage 1's other constructs.

### 5.4 No Disambiguation Between No-payload Variants and Bindings at Parse Time

Because `None` and a variable named `none` both lex as `Ident`, the parser cannot distinguish a no-payload variant pattern from a fresh binding without type information. Stage 2 chooses to defer this distinction to the semantic phase, parsing both as `PatternKind::Ident(name)`. The semantic phase resolves `name` against the scrutinee's enum scope and rewrites or annotates the AST accordingly. This is consistent with the spec, which does not require any naming convention (e.g., capitalization) to disambiguate.

## 6. Alternatives Considered

### 6.1 Match Arm Boundary

**Speculative pattern parsing.** The original spec form `Pattern then body` requires the parser to lookahead through a syntactic pattern and check whether `then` follows. This was rejected for two reasons: error messages near arm boundaries become unreliable when speculative parses succeed against unintended input, and the parser logic gains a save/restore facility that is otherwise unnecessary in this codebase.

**Pipe separator (`| Pattern then body`).** OCaml and F# use `|` to separate arms. This was rejected because `|` is currently unused in Dyne and introducing it for a single grammar slot creates an asymmetry with the rest of the language, which uses keyword-bracketed forms (`if/then/end`, `while/do/end`).

**`case` keyword (chosen).** Adds one keyword, adds a single-token boundary check, aligns with Scala/Swift/Erlang/Python 3.10+ conventions, and matches the keyword-bracketed style of the rest of the language.

### 6.2 Literal Patterns Inclusion

**No literal patterns.** Forces users to write `case Some(x) then if x == 0 then ... end` instead of `case Some(0) then ...`. Rejected as needlessly restrictive for an idiom that is common in pattern-matching languages.

**Integer + boolean only.** Conservative but excludes string patterns, which are inexpensive to add and useful for tag-based dispatch. Rejected.

**Integer + boolean + string (chosen).** Matches the literal types where equality is well-defined (string equality is exact, boolean and integer equality are exact). Excludes floats, which is correct for this language. Aligns with Rust's effective set after float patterns were deprecated.

**All literal types including float.** Rejected for the reasons in §5.2.

### 6.3 Float Pattern Handling

**Allow silently.** Rejected; encourages misuse.

**Allow with semantic-phase warning.** Rejected; the warning would still let invalid code compile in a future where the warning is suppressed or missed. Fail-fast at parse time is more robust.

**Reject at parse time (chosen).** The narrowest enforcement point, and the one where the educational error message is most likely to be read.

### 6.4 Struct Destructuring Patterns

Spec §4.6 does not show struct destructuring (`State { q, p, t }` in match position), and the current pattern AST does not model named-field patterns. Adding the syntax requires a new `Pattern::Struct(String, Vec<(String, Pattern)>)` variant and extra parser logic to disambiguate it from variant patterns. Stage 2 omits the feature entirely: users who need decomposition can bind the whole struct and access its fields by name. If real usage shows this is a common pain point, a follow-up PR can add it without breaking anything Stage 2 ships.

## 7. Open Items

- **No-payload variant disambiguation policy.** Stage 2 parses `None` as `Pattern::Ident("None")` and defers resolution to the semantic phase. The semantic phase will need an explicit rule (lookup against the scrutinee's enum, error on shadowing, etc.). The rule is out of scope here but should be settled before the type checker design begins.
- **Pattern in `let` and function parameters.** The spec does not show patterns in irrefutable positions. If `let Some(x) = opt` becomes desirable later, refutability checking will need to be designed alongside it. Out of scope for Stage 2.
- **Floating-point pattern error wording.** The exact message proposed in §4.6 is illustrative; the final wording is a small detail that can be tuned during implementation review.

## 8. Future Extensions

The following items are explicitly outside Stage 2 but are worth flagging as natural follow-ups:

- **Range patterns.** `case 0..=10 then ...` — common in Rust/Scala/Swift/F#. Useful for physics ranges (e.g., bounding integer indices). Adds `PatternKind::Range` and a small grammar extension.
- **Or-patterns.** `case Some(1) | Some(2) then ...` — common in OCaml/Scala/Python. Adds `PatternKind::Or(Vec<Pattern>)` and a grammar extension; mostly useful once literal patterns are in.
- **Struct destructuring patterns.** As discussed in §6.4.
- **Generic struct definitions.** `struct Pair<A, B>` for user-defined parametric data. Trivial extension once a use case appears.

## 9. Approval

This Design Doc is finalized once CityBear3 approves. Approval transitions the work to `/create-plan`, which decomposes the design into TDD-friendly implementation tasks. The implementation will reuse the agent-teams flow established for Stage 1.
