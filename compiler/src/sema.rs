//! Semantic analysis (Stage 3): name resolution and type checking.
//!
//! PR-3a populates the resolution side of this module. PR-3b adds basic
//! type checking; later PRs add generics, units, and stdlib signatures.

pub mod check;
pub mod diag;
pub mod resolve;
pub mod ty;

use std::collections::HashMap;

use crate::ast::{Item, Program};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{Ty, VariantPayload, lower_type};

/// Per-expression types keyed by `NodeId`. Populated in Pass 2 by
/// Tasks 4–6; Task 3 leaves it empty.
pub type TypeTable = HashMap<NodeId, Ty>;

/// Per-DefId types for `Function`/`Param`/`LocalLet`/`TopLevelLet`/
/// `LoopVar`/`PatternBinding` definitions.
pub type DefTypeMap = HashMap<DefId, Ty>;

/// Struct DefId → ordered `(field_name, field_ty)` pairs.
pub type StructFieldMap = HashMap<DefId, Vec<(String, Ty)>>;

/// `EnumVariant` DefId → `VariantPayload` (parent enum + payload Tys).
pub type VariantPayloadMap = HashMap<DefId, VariantPayload>;

/// The output of `check()`. Aggregates the parsed program with all
/// annotation tables produced by sema phases.
///
/// `TypedProgram` is constructed only by `sema::check`; the private
/// constructor enforces the phase boundary at compile time. Stage 4
/// will accept `&TypedProgram` rather than `Program`.
#[derive(Debug)]
#[non_exhaustive]
pub struct TypedProgram {
    pub program: Program,
    pub types: TypeTable,
    pub resolutions: ResolveTable,
    pub definitions: DefinitionTable,
    /// Per-DefId types for `Function` (`Ty::Function` variant), `Param`,
    /// `LocalLet`, `TopLevelLet`, `LoopVar`, `PatternBinding`. Populated by
    /// Pass 1 (`signature_pass`) for top-level signatures and params; later
    /// passes (Tasks 4–6) populate local bindings.
    pub def_types: DefTypeMap,
    /// Struct DefId → ordered `(field_name, field_ty)` pairs.
    pub struct_fields: StructFieldMap,
    /// `EnumVariant` DefId → `VariantPayload` (parent enum DefId + payload Tys).
    pub variant_payloads: VariantPayloadMap,
}

impl TypedProgram {
    #[allow(clippy::too_many_arguments)]
    fn new(
        program: Program,
        types: TypeTable,
        resolutions: ResolveTable,
        definitions: DefinitionTable,
        def_types: DefTypeMap,
        struct_fields: StructFieldMap,
        variant_payloads: VariantPayloadMap,
    ) -> Self {
        Self {
            program,
            types,
            resolutions,
            definitions,
            def_types,
            struct_fields,
            variant_payloads,
        }
    }
}

/// Run the semantic-analysis phases over a parsed program.
///
/// Pass 1 (Task 3) lowers top-level signatures into per-DefId tables so
/// Pass 2 (Tasks 4–6) can type-check function bodies with mutual-recursion
/// support. Pass 2 currently leaves the per-expression `types` table empty.
pub fn check(program: Program) -> Result<TypedProgram, Vec<Diagnostic>> {
    let (resolutions, definitions, mut diags) = resolve::resolve_program(&program);

    // Pass 1: lower top-level signatures (functions, structs, enum variants,
    // top-level lets, function params). Continues even when `diags` already
    // contains resolve errors — `lower_type`'s `Ty::Error` sentinel
    // suppresses cascading diagnostics from sub-trees that failed earlier.
    let (mut def_types, struct_fields, variant_payloads) =
        signature_pass(&program, &resolutions, &definitions, &mut diags);

    // Pass 2: bidirectional type checking of function bodies and top-level
    // let init expressions. Task 4 lands literal/ident/operator rules; later
    // tasks extend Pass 2 to calls / struct literals / control flow / match.
    let (types, type_diags) = check::run(
        &program,
        &resolutions,
        &definitions,
        &mut def_types,
        &struct_fields,
        &variant_payloads,
    );
    diags.extend(type_diags);

    if !diags.is_empty() {
        return Err(diags);
    }
    Ok(TypedProgram::new(
        program,
        types,
        resolutions,
        definitions,
        def_types,
        struct_fields,
        variant_payloads,
    ))
}

/// Walks each top-level item, lowering its declared types into the per-
/// definition tables. Function param DefIds get their types here so Pass 2
/// (function body walks) can read them. Top-level `Item::Let` gets its
/// declared type recorded; the init expression is type-checked in Pass 2.
fn signature_pass(
    program: &Program,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    diags: &mut Vec<Diagnostic>,
) -> (DefTypeMap, StructFieldMap, VariantPayloadMap) {
    let mut def_types: DefTypeMap = HashMap::new();
    let mut struct_fields: StructFieldMap = HashMap::new();
    let mut variant_payloads: VariantPayloadMap = HashMap::new();

    // Reverse-name index over hoisted top-level definitions (functions,
    // structs, enums, variants, top-level lets). Lets us recover each item's
    // DefId from `.name`. Per-pass build — not stored on TypedProgram.
    let name_to_def: HashMap<&str, DefId> = definitions
        .iter()
        .filter(|(_, info)| {
            matches!(
                info.kind,
                DefKind::Function
                    | DefKind::Struct
                    | DefKind::Enum
                    | DefKind::EnumVariant
                    | DefKind::TopLevelLet
            )
        })
        .map(|(id, info)| (info.name.as_str(), *id))
        .collect();

    for item in &program.items {
        match item {
            Item::Function(f) => {
                let Some(def_id) = name_to_def.get(f.name.as_str()).copied() else {
                    continue;
                };
                let param_tys: Vec<Ty> = f
                    .params
                    .iter()
                    .map(|p| lower_type(&p.ty, resolutions, definitions, diags))
                    .collect();
                let ret_ty = lower_type(&f.return_ty, resolutions, definitions, diags);
                // Param DefIds aren't in `name_to_def` (function-scoped, not
                // hoisted). Recover each via `DefinitionTable` matching
                // `(DefKind::Param, name, span)` and reuse the already-lowered
                // Ty so `lower_type` runs once per param. O(params ×
                // definitions); acceptable for dyne-scale code. A future PR
                // can add a `param_def_ids: HashMap<NodeId, DefId>` index to
                // Resolver output if profiling shows it hot.
                for (p, ty) in f.params.iter().zip(param_tys.iter()) {
                    let Some(p_def_id) = definitions
                        .iter()
                        .find(|(_, info)| {
                            matches!(info.kind, DefKind::Param)
                                && info.name == p.name
                                && info.span == p.span
                        })
                        .map(|(id, _)| *id)
                    else {
                        continue;
                    };
                    def_types.insert(p_def_id, ty.clone());
                }
                def_types.insert(def_id, Ty::Function(param_tys, Box::new(ret_ty)));
            }
            Item::Struct(s) => {
                let Some(def_id) = name_to_def.get(s.name.as_str()).copied() else {
                    continue;
                };
                let fields: Vec<(String, Ty)> = s
                    .fields
                    .iter()
                    .map(|field| {
                        (
                            field.name.clone(),
                            lower_type(&field.ty, resolutions, definitions, diags),
                        )
                    })
                    .collect();
                struct_fields.insert(def_id, fields);
            }
            Item::Enum(e) => {
                let Some(enum_def_id) = name_to_def.get(e.name.as_str()).copied() else {
                    continue;
                };
                for variant in &e.variants {
                    let Some(variant_def_id) = name_to_def.get(variant.name.as_str()).copied()
                    else {
                        continue;
                    };
                    let payload: Vec<Ty> = variant
                        .payload
                        .iter()
                        .map(|t| lower_type(t, resolutions, definitions, diags))
                        .collect();
                    variant_payloads.insert(
                        variant_def_id,
                        VariantPayload {
                            parent_enum: enum_def_id,
                            payload,
                        },
                    );
                }
            }
            Item::Let(l) => {
                let Some(def_id) = name_to_def.get(l.name.as_str()).copied() else {
                    continue;
                };
                let ty = lower_type(&l.ty, resolutions, definitions, diags);
                def_types.insert(def_id, ty);
            }
            Item::Import(_) => {}
        }
    }

    (def_types, struct_fields, variant_payloads)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Program;
    use crate::lexer::tokenize;
    use crate::parser::parse;

    fn parse_src(src: &str) -> Program {
        parse(tokenize(src).unwrap()).unwrap()
    }

    #[test]
    fn check_valid_program_returns_typed_program() {
        let prog = parse_src("let x: Int = 1");
        let typed = check(prog).expect("expected ok");
        assert_eq!(typed.program.items.len(), 1);
        // PR-3b's Pass 2 records expression types. The init `1` is checked
        // against `Int` and its `NodeId → Ty::Int` mapping lands in `types`.
        assert!(
            !typed.types.is_empty(),
            "PR-3b records expression types in Pass 2"
        );
        assert_eq!(
            typed.definitions.len(),
            1,
            "the top-level let is the only def"
        );
    }

    #[test]
    fn check_program_with_undefined_name_returns_err() {
        let prog = parse_src("function f(): Int\n  return undefined_var\nend");
        let diags = check(prog).expect_err("expected sema error");
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].phase, crate::diag::Phase::Sema);
        assert!(diags[0].message.contains("undefined_var"));
    }

    #[test]
    fn check_program_with_multiple_undefined_names_returns_all() {
        let prog = parse_src("function f(): Int\n  let x: Int = a + b\n  return c\nend");
        let diags = check(prog).expect_err("expected sema errors");
        // Three undefined names → exactly three diagnostics; pin the names
        // and order so a regression that emits a single name twice (or
        // skips one) fails loudly.
        assert_eq!(
            diags.len(),
            3,
            "expected exactly 3 diagnostics for a/b/c, got {:?}",
            diags
        );
        assert!(diags[0].message.contains("`a`"));
        assert!(diags[1].message.contains("`b`"));
        assert!(diags[2].message.contains("`c`"));
    }

    #[test]
    fn check_typed_program_resolutions_keyed_by_node_id() {
        let prog = parse_src("let k: Scalar = 0.5\nfunction f(): Scalar\n  return k\nend");
        let typed = check(prog).expect("expected ok");
        // The Ident("k") inside f's body has its own NodeId; that NodeId
        // must appear in the resolutions table.
        assert!(!typed.resolutions.is_empty());
        // And every value in the table maps to a DefId that exists in
        // definitions.
        for def_id in typed.resolutions.values() {
            assert!(typed.definitions.contains_key(def_id));
        }
    }

    // ----- PR-3b Task 3: signature pre-pass populates type tables -----

    #[test]
    fn check_populates_function_signature_in_def_types() {
        use crate::sema::resolve::DefKind;
        use crate::sema::ty::Ty;
        let prog = parse_src("function add(a: Int, b: Int): Int\n  return 0\nend");
        let typed = check(prog).expect("ok");
        let func_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| matches!(info.kind, DefKind::Function))
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&func_def_id).unwrap();
        assert_eq!(
            *sig,
            Ty::Function(vec![Ty::Int, Ty::Int], Box::new(Ty::Int))
        );
    }

    #[test]
    fn check_populates_struct_fields() {
        use crate::sema::resolve::DefKind;
        let prog = parse_src("struct Point\n  x: Scalar\n  y: Scalar\nend");
        let typed = check(prog).expect("ok");
        let struct_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| matches!(info.kind, DefKind::Struct))
            .map(|(id, _)| *id)
            .unwrap();
        let fields = typed.struct_fields.get(&struct_def_id).unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].0, "x");
        assert_eq!(fields[1].0, "y");
    }

    #[test]
    fn check_populates_enum_variant_payloads() {
        use crate::sema::ty::Ty;
        let prog = parse_src("enum Shape\n  Circle(Int)\n  Empty\nend");
        let typed = check(prog).expect("ok");
        let circle_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Circle")
            .map(|(id, _)| *id)
            .unwrap();
        let payload = typed.variant_payloads.get(&circle_def_id).unwrap();
        assert_eq!(payload.payload.len(), 1);
        assert_eq!(payload.payload[0], Ty::Int);

        let empty_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Empty")
            .map(|(id, _)| *id)
            .unwrap();
        let empty_payload = typed.variant_payloads.get(&empty_def_id).unwrap();
        assert!(empty_payload.payload.is_empty());
    }

    #[test]
    fn check_populates_param_def_types() {
        use crate::sema::resolve::DefKind;
        use crate::sema::ty::Ty;
        let prog = parse_src("function f(x: Int): Int\n  return x\nend");
        let typed = check(prog).expect("ok");
        let param_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| matches!(info.kind, DefKind::Param))
            .map(|(id, _)| *id)
            .unwrap();
        assert_eq!(*typed.def_types.get(&param_def_id).unwrap(), Ty::Int);
    }

    #[test]
    fn check_populates_top_level_let_def_type() {
        use crate::sema::resolve::DefKind;
        use crate::sema::ty::{Dimension, Ty};
        let prog = parse_src("let pi: Scalar = 3.14");
        let typed = check(prog).expect("ok");
        let let_def_id = typed
            .definitions
            .iter()
            .find(|(_, info)| matches!(info.kind, DefKind::TopLevelLet))
            .map(|(id, _)| *id)
            .unwrap();
        assert_eq!(
            *typed.def_types.get(&let_def_id).unwrap(),
            Ty::Scalar(Dimension::ZERO)
        );
    }

    // ----- Negative regression tests: signature_pass must not duplicate
    // diagnostics for an invalid annotation that's already been reported by
    // a single `lower_type` call. Pre-fix, `Item::Function` lowered each
    // param twice (once in the main arm, once in a trailing recovery loop),
    // emitting `Ty::Error` diagnostics in duplicate.

    #[test]
    fn invalid_param_type_emits_single_diagnostic() {
        let prog = parse_src("function f(v: Vec): Int\n  return 0\nend");
        let err = check(prog).expect_err("expected diags");
        assert_eq!(err.len(), 1, "got: {:?}", err);
        assert!(err[0].message.contains("`Vec`"));
    }

    #[test]
    fn invalid_return_type_emits_single_diagnostic() {
        let prog = parse_src("function f(): Vec\n  return 0\nend");
        let err = check(prog).expect_err("expected diags");
        assert_eq!(err.len(), 1, "got: {:?}", err);
        assert!(err[0].message.contains("`Vec`"));
    }

    #[test]
    fn invalid_struct_field_type_emits_single_diagnostic() {
        let prog = parse_src("struct S\n  x: Vec\nend");
        let err = check(prog).expect_err("expected diags");
        assert_eq!(err.len(), 1, "got: {:?}", err);
        assert!(err[0].message.contains("`Vec`"));
    }
}
