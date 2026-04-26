# Design Doc: Calculator コンパイラ フロントエンド

| | |
|---|---|
| Status | Draft |
| Author | CityBear3 (design ownership) / Claude Code (drafter by delegation) |
| Created | 2026-04-22 |
| Scope | Lexer / Parser / AST 層のアーキテクチャ |
| 前提 | `docs/language-spec.md` v1（現行）、`docs/product-spec.md` |

## 1. 概要

Calculator コンパイラのフロントエンド（字句解析・構文解析・AST）を Rust 2024 で実装する。最初のバックエンドは **AST インタプリタ** とし、ヒープ確保を伴う型（`String` / `Array<T>` / `Dict<K,V>`）は Rust の所有権機構に委譲する。フロントエンドのデータ構造は**言語仕様フル**を表現可能な形で設計するが、Parser 実装は段階的に拡張する。

## 2. コンテキスト

Calculator は `docs/language-spec.md` で定義された計算物理向けコンパイル言語で、仕様上は単位型、`Vec<N>` / `Mat<M,N>` の静的次元検査、網羅的パターンマッチ、自動微分などを備える。現時点では `compiler/src/main.rs` に `Lexer` 構造体のスタブと初期化テストがあるのみで、実装はゼロ地点。

## 3. ゴール / 非ゴール

### ゴール

- `language-spec.md` に書かれた全言語機能を**表現可能**な AST を定義する
- Lexer・Parser を手書きで実装し、仕様のプリミティブ部分（数値計算・関数・制御フロー・型注釈・単位型注釈）をパースできる状態に到達する
- エラー発生位置を行・列単位で提示できる基盤（`Span`）を整備する
- 後続フェーズ（型検査・意味解析・インタプリタ）が AST を消費して動けるようにする

### 非ゴール

- 型検査・意味解析の実装（後段 Design Doc）
- インタプリタの実装（後段 Design Doc）
- ネイティブコード生成、LLVM バックエンド
- 独自のメモリ管理機構（Rust 所有権に委譲、将来のネイティブバックエンド時に再検討）
- 複数エラーの蓄積 / Parser エラーリカバリ（将来拡張）
- 文字列補間、マクロ、属性（仕様外）

## 4. スコープ: 言語機能カバレッジ

### AST でサポート（構造として用意）

仕様の全機能に対応する AST ノードを定義する:

- プリミティブ型: `Scalar`, `Int`, `Bool`, `String`
- コレクション型: `Vec<N>`, `Mat<M,N>`, `Array<T>`, `Dict<K,V>`
- 関数型: `Fn(...) -> T`
- 単位型注釈（型引数の最終要素）
- `let` / 再代入
- 関数定義 / 匿名関数（単行・複数行）
- 制御フロー: `if`/`elseif`/`else`, `for` レンジ, `for in`, `while`
- `struct` 定義・リテラル・フィールドアクセス
- `enum` 定義 + `match` 式（網羅性は後段で検査）
- `import`
- 演算子: 算術 / 比較 / 論理
- ベクトル・行列リテラル

### Parser 実装の優先順位

AST 定義が完成した上で、Parser の実装は以下の順に段階的に進める（本 Design Doc の範囲は段階 1 まで）:

1. **段階 1 (本ドキュメント範囲)**: 型注釈（単位型含む）、`let`、関数定義、式、制御フロー、ベクトル・行列リテラル
2. 段階 2: `struct` / `enum` 定義、`match` 式
3. 段階 3: 匿名関数（キャプチャなし → ありの順）
4. 段階 4: `import`、`Array` / `Dict` リテラルおよび関連操作

## 5. アーキテクチャ

### 5.1 パイプライン

```
source: &str
   │
   ▼
┌────────┐      Vec<Token>      ┌────────┐      Program      ┌─────────┐
│ Lexer  │ ──────────────────▶ │ Parser │ ────────────────▶ │ AST     │
└────────┘                      └────────┘                    └─────────┘
   │                              │
   └──── Err(CompileError) ───────┤
                                  ▼
                             fail-fast
```

- 各フェーズは `Result<T, CompileError>` を返す
- 最初のエラーで停止（**fail-fast**）
- トークン列は一括生成して Parser に渡す（ストリーミングはしない）

### 5.2 クレート構成

単一 `compiler` クレート。Rust 2024 edition の慣例 (`foo.rs` + `foo/`) に従う。

```
compiler/
├── Cargo.toml              # ゼロ依存
└── src/
    ├── main.rs             # CLI エントリ（薄いラッパ）
    ├── lib.rs              # pub fn compile(source: &str) -> Result<Program, CompileError>
    ├── source.rs           # SourceFile, Span, 行・列算出
    ├── error.rs            # CompileError, ErrorKind, 診断整形
    ├── lexer.rs            # pub mod token; pub mod scanner;
    ├── lexer/
    │   ├── token.rs        # Token, TokenKind
    │   └── scanner.rs      # tokenize(&str) -> Result<Vec<Token>, CompileError>
    ├── parser.rs           # pub mod expr; pub mod stmt; pub mod types;
    ├── parser/
    │   ├── expr.rs         # Pratt parser
    │   ├── stmt.rs         # 再帰下降
    │   └── types.rs        # 型式パーサ (Vec<N>, Scalar<kg>, Fn(...)->T)
    ├── ast.rs              # pub mod expr; pub mod stmt; pub mod ty; pub mod item;
    └── ast/
        ├── expr.rs
        ├── stmt.rs
        ├── ty.rs
        └── item.rs         # Program, Item (Function, Struct, Enum, Import, Let)
```

**依存: ゼロ**。`logos` / `thiserror` / `codespan-reporting` 等は使わない。

### 5.3 モジュール責務

| モジュール | 責務 | 後続フェーズが触るか |
|---|---|---|
| `source` | 元ソースの保持、バイトオフセットから行・列の算出 | 型検査・診断で参照 |
| `error` | 単一のエラー型、行番号付き整形出力 | 全フェーズが生成 |
| `lexer::token` | トークン型定義 | Parser のみ |
| `lexer::scanner` | 文字列 → トークン列 | エントリポイントから呼ぶ |
| `parser::{expr,stmt,types}` | トークン列 → AST | エントリポイントから呼ぶ |
| `ast::*` | AST 型定義（不変ツリー） | 全後続フェーズの入力 |

## 6. 設計決定

### 6.1 ソース位置 (`Span`)

```rust
pub struct Span {
    pub start: usize,  // バイトオフセット
    pub end: usize,    // exclusive
}
```

- すべての `Token` と AST ノードが `Span` を持つ
- 行・列は表示時に `SourceFile` から逐次計算（事前テーブルは YAGNI）
- `Span::merge(a, b)` で合成できるようにする

### 6.2 エラー型

```rust
pub struct CompileError {
    pub kind: ErrorKind,
    pub span: Span,
    pub message: String,
}

pub enum ErrorKind {
    Lex,
    Parse,
    // 将来: Type, Unit, Exhaustiveness, ...
}
```

- `thiserror` は使わず `Display` を手書き
- 診断整形は `error.rs` が `SourceFile` を受け取って行抜粋付きで出力

### 6.3 Token

```rust
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub enum TokenKind {
    // リテラル
    Int(i64), Float(f64), Str(String), Ident(String),

    // キーワード
    Let, Function, End, Return,
    If, Then, Elseif, Else,
    For, In, Do, While,
    Match, Struct, Enum, Import,
    And, Or, Not, True, False,

    // 演算子
    Plus, Minus, Star, Slash, Caret,
    Eq, EqEq, Neq, Lt, Gt, Le, Ge,
    Colon, Comma, Dot, Arrow,            // `->`
    LParen, RParen,
    LBracket, RBracket,
    LBrace, RBrace,

    // 構造
    Newline,
    Eof,
}
```

- 識別子・文字列は `String` 所有（**interning は YAGNI**）
- `Newline` は明示トークン。Parser 側で文境界として消費 or スキップ
- コメント (`// ...`) はスキャン段階で破棄

### 6.4 Lexer

手書きステートマシン、単一パス、バイト走査（UTF-8 は識別子・文字列内で透過）。

```rust
pub fn tokenize(source: &str) -> Result<Vec<Token>, CompileError>
```

主な走査規則:

- ASCII 空白・タブはスキップ
- `\n` / `\r\n` は `Newline` トークンとして出す（連続する改行は 1 個に畳む）
- `//` から行末までコメント
- 数字で始まる場合、小数点・指数を含むか見て `Int` / `Float` を選ぶ
- `a-zA-Z_` で始まる識別子を読み取り、キーワードテーブルと照合
- `"..."` で文字列リテラル（エスケープは `\n` / `\t` / `\\` / `\"` を最小サポート）
- 記号は先読み 1〜2 文字で決定（`=` vs `==`、`!` vs `!=`、`-` vs `->`、`<` vs `<=` 等）

### 6.5 AST

ツリー構造、`Box` で再帰、すべてのノードが `Span` を持つ。

#### トップレベル

```rust
pub struct Program {
    pub items: Vec<Item>,
}

pub enum Item {
    Import(ImportItem),
    Function(FunctionDef),
    Let(LetStmt),
    Struct(StructDef),
    Enum(EnumDef),
}
```

#### 式

```rust
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub enum ExprKind {
    // リテラル
    IntLit(i64),
    FloatLit(f64),
    StrLit(String),
    BoolLit(bool),
    VecLit(Vec<Expr>),
    MatLit(Vec<Vec<Expr>>),

    // 参照
    Ident(String),

    // 演算
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnaryOp(UnaryOp, Box<Expr>),

    // アクセス
    Call(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    FieldAccess(Box<Expr>, String),

    // 複合
    Lambda(LambdaExpr),
    StructLit(String, Vec<(String, Expr)>),
    If(IfExpr),
    Match(Box<Expr>, Vec<MatchArm>),
    Block(Block),
}

pub enum BinOp {
    Add, Sub, Mul, Div, Pow,
    Eq, Neq, Lt, Gt, Le, Ge,
    And, Or,
}

pub enum UnaryOp {
    Neg, Not,
}
```

#### 文・ブロック

```rust
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

pub enum StmtKind {
    Let(LetStmt),
    Assign(String, Expr),            // x = expr
    Expr(Expr),
    Return(Option<Expr>),
    For(ForStmt),
    While(WhileStmt),
}

pub struct LetStmt {
    pub name: String,
    pub ty: Type,
    pub init: Expr,
}

pub enum ForStmt {
    Range { var: String, start: Expr, end: Expr, body: Block },
    Iter  { var: String, iter: Expr, body: Block },
    IterKV { key: String, value: String, iter: Expr, body: Block },
}

pub struct WhileStmt { pub cond: Expr, pub body: Block }
```

#### 型

```rust
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

pub enum TypeKind {
    Named(String),                           // Scalar, Int, Bool, String, ユーザ型
    Generic(String, Vec<TypeArg>),           // Vec<3>, Mat<2,3>, Scalar<kg>, Array<T>
    Function(Vec<Type>, Box<Type>),          // Fn(T, U) -> V
}

pub enum TypeArg {
    Type(Type),
    Int(i64),                                // Vec<3> の 3
    Unit(UnitExpr),                          // Scalar<kg*m/s^2>
}

pub struct UnitExpr {
    pub kind: UnitExprKind,
    pub span: Span,
}

pub enum UnitExprKind {
    Atom(String),                            // kg, m, s
    Mul(Box<UnitExpr>, Box<UnitExpr>),
    Div(Box<UnitExpr>, Box<UnitExpr>),
    Pow(Box<UnitExpr>, i64),                 // m^2
}
```

**ポイント**:
- `Vec<3>` と `Scalar<kg>` は同じ `Generic` で表現し、意味解析で区別する
- `TypeArg` で数値・単位式・型を区別する。Parser は型引数位置で専用パースする

#### 関数 / 匿名関数 / 構造体 / 列挙型

```rust
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<Param>,
    pub return_ty: Type,
    pub body: Block,
    pub span: Span,
}

pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

pub struct LambdaExpr {
    pub params: Vec<Param>,
    pub return_ty: Option<Type>,    // 型推論の余地を残す
    pub body: LambdaBody,
}

pub enum LambdaBody {
    Expr(Box<Expr>),                // (x) -> x^2
    Block(Block),                   // (q) -> \n ... \n end
}

pub struct StructDef {
    pub name: String,
    pub fields: Vec<StructField>,
    pub span: Span,
}

pub struct StructField { pub name: String, pub ty: Type, pub span: Span }

pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<String>,   // enum Option<T>
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

pub struct EnumVariant {
    pub name: String,
    pub payload: Vec<Type>,         // Ok(T) → [T], None → []
    pub span: Span,
}
```

#### if / match

```rust
pub struct IfExpr {
    pub cond: Box<Expr>,
    pub then_block: Block,
    pub elseifs: Vec<(Expr, Block)>,
    pub else_block: Option<Block>,
}

pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Block,
    pub span: Span,
}

pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

pub enum PatternKind {
    Wildcard,                              // `_`（将来予約、仕様では未明言）
    Ident(String),                         // Ok(f) の f
    Variant(String, Vec<Pattern>),         // Ok(f), Some(x), Total(a, b)
}
```

### 6.6 Parser

手書き再帰下降、式は Pratt パーサ。

```rust
pub fn parse(tokens: Vec<Token>) -> Result<Program, CompileError>

struct Parser<'t> {
    tokens: &'t [Token],
    pos: usize,
}

impl<'t> Parser<'t> {
    fn peek(&self) -> &Token;
    fn peek_kind(&self) -> &TokenKind;
    fn advance(&mut self) -> &Token;
    fn expect(&mut self, kind: TokenKindDiscriminant) -> Result<&Token, CompileError>;
    fn consume_newlines(&mut self);
    fn at(&self, kind: TokenKindDiscriminant) -> bool;
}
```

#### 式の優先順位 (低 → 高)

| 優先度 | 演算子 | 結合 |
|---|---|---|
| 1 | `or` | 左 |
| 2 | `and` | 左 |
| 3 | `not` (単項) | — |
| 4 | `==` `!=` `<` `>` `<=` `>=` | 左 |
| 5 | `+` `-` | 左 |
| 6 | `*` `/` | 左 |
| 7 | 単項 `-` | — |
| 8 | `^` | **右** |
| 9 | 関数呼び出し / インデックス / フィールドアクセス | 左 |

`not` と 単項 `-` は Pratt parser の prefix operator として実装する。`not` は比較・算術以上を取り込む（`not 1 + 2 == not (1 + 2)`、Python と同じ）、単項 `-` は `^` を取り込むが call/index/field よりは弱い（`-x^2 == -(x^2)`、Python/Fortran と同じ。物理計算で頻出する Gaussian `e^(-x^2)` などが直感通りに書ける）。

#### 文境界

- 文は `Newline` で区切られる。文末には `Newline` / `Eof` / ブロック終端トークン (`end` / `else` / `elseif`) のいずれかが必須
- `then` / `do` の直後の `Newline` はブロック開始とみなす（任意 — 1 行 if/while/for もサポート、例 `if x > 0 then return 1 end`）
- `end` / `else` / `elseif` がブロックの閉じ
- Vec / Mat リテラル内 (`[ ... ]`) では `Newline` を無視する（multi-line 記法のサポート）。trailing comma も許可

#### 型引数のパース

`<` を見たら型引数モードに入り、以下を区別:
- 先頭が数字 → `TypeArg::Int`
- 識別子列で `/` `*` `^` を含む → `TypeArg::Unit`
- それ以外 → `TypeArg::Type`

## 7. 検討した代替案

### 7.1 AST スコープ

| 案 | 内容 | 採否 |
|---|---|---|
| MVP サブセット | 数値・関数・制御フローのみ | 却下（単位型・enum を後付けすると AST を書き直す羽目に） |
| 中間（拡張点を残す最小） | AST は最小、型 enum だけ拡張点を切る | 却下（struct/enum も後で追加する際の手戻りが残る） |
| **仕様フル** | 仕様全機能を AST に載せる、Parser は段階実装 | **採用** |

### 7.2 バックエンド戦略

| 案 | 内容 | 採否 |
|---|---|---|
| heap-free サブセット先行 | Array/String/Dict 抜きで動かす | 却下（`printf` すら使えない制約がきつい） |
| **AST インタプリタ + Rust 所有権** | heap 型は Rust 任せ、ネイティブは将来課題 | **採用** |
| メモリ管理を先に自作 | GC/arena をランタイム実装してから開始 | 却下（実使用データなしに方式決定するリスク、言語検証が遅れる） |

### 7.3 外部依存

| 案 | 内容 | 採否 |
|---|---|---|
| **ゼロ依存** | 全手書き | **採用**（エラーメッセージ品質の制御、学習価値） |
| 最小（`thiserror` のみ） | エラー定義の boilerplate 削減 | 却下（手書きで十分） |
| 実用クレート許容 | `logos`, `codespan-reporting` など | 却下（過剰） |

### 7.4 エラー戦略

| 案 | 内容 | 採否 |
|---|---|---|
| **Fail-fast** | 最初のエラーで停止 | **採用** |
| エラー蓄積 + リカバリ | Vec<CompileError> を返す | 却下（実装量が大、将来拡張） |

### 7.5 AST メモリ表現

| 案 | 内容 | 採否 |
|---|---|---|
| **ツリー + `Box`** | 素直な Rust enum、所有権ベース | **採用** |
| アリーナ + インデックス | `Vec<Node>` + `NodeId(u32)` | 却下（最適化。性能課題が出たら再検討） |

## 8. オープンな論点

- **エスケープシーケンスの範囲**: 仕様には `"Hello, World"` しか例がない。最小は `\n \t \\ \"` としたが、`\r` `\0` `\xNN` `\u{...}` まで必要か？ 初期実装では最小のみ、拡張は要望ベース。
- **パターンマッチのワイルドカード (`_`)**: 仕様書には明記がないが、網羅性のために将来必要になる可能性。AST には `Wildcard` variant を用意しておき、Parser では当面エラーにする。
- **浮動小数点リテラル形式**: `1.` や `.5` は許すか？ 仕様例は両側に数字がある形のみ。初期実装は両側数字必須とし、議論の余地を残す。
- **演算子 `!=` vs `not`**: 仕様では比較に `!=`、論理否定に `not` が使われる。`!` 単独は未使用なので将来予約に留めるか、当面はトークン化しない。

## 9. 将来の拡張ポイント

本 Design Doc の範囲外だが、AST 設計上考慮している拡張点:

- **型検査・単位検査**: `ast::ty::Type` と `TypeArg::Unit` を入力として別モジュールで実装
- **パターン網羅性検査**: `MatchArm` の `pattern` に対して別パスで検証
- **AST インタプリタ**: `Program` を入力として別クレート or モジュールで実装
- **エラー蓄積**: `Parser` に `errors: Vec<CompileError>` フィールドを追加し、recover 関数で同期点まで飛ばす形で後付け可能
- **ネイティブバックエンド / メモリ管理**: 本 Design Doc の範囲外。`Array` / `Dict` / `String` のランタイム表現を決めるタイミングで別 Design Doc を起こす

## 10. 承認

本 Design Doc は CityBear3 の承認をもって確定。確定後 `/create-plan` に進む。
