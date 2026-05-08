//! Semantic analysis (Stage 3): name resolution and type checking.
//!
//! PR-3a populates the resolution side of this module. PR-3b adds basic
//! type checking; later PRs add generics, units, and stdlib signatures.

pub mod check;
pub mod diag;
pub mod exhaust;
pub mod resolve;
pub mod ty;
pub mod unify;

pub(crate) mod builtins;

use std::collections::HashMap;

use crate::ast::{Item, Program};
use crate::diag::Diagnostic;
use crate::ids::{DefId, NodeId};
use crate::sema::resolve::{BindingTable, DefKind, DefinitionTable, ResolveTable};
use crate::sema::ty::{ParamSubst, Ty, VariantPayload, lower_type, lower_type_with_subst};

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
    /// Use-site NodeId → DefId. Maps every resolved name *use* to the
    /// definition it refers to. Orthogonal to `binding_def_ids` below.
    pub resolutions: ResolveTable,
    pub definitions: DefinitionTable,
    /// Binding-intro NodeId → DefId. Maps every binding *introduction* to
    /// the DefId allocated for it. Populated by `define_or_report` for
    /// Function, Struct, Enum, EnumVariant, Param, LocalLet, TopLevelLet,
    /// and PatternBinding intro sites. Loop-var bindings are not yet
    /// recorded; consult `check.rs::loop_var_def_id` for those.
    pub binding_def_ids: BindingTable,
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

/// Run the semantic-analysis phases over a parsed program.
///
/// Pass 1 (Task 3) lowers top-level signatures into per-DefId tables so
/// Pass 2 (Tasks 4–6) can type-check function bodies with mutual-recursion
/// support. Pass 2 currently leaves the per-expression `types` table empty.
pub fn check(program: Program) -> Result<TypedProgram, Vec<Diagnostic>> {
    let (resolutions, definitions, binding_def_ids, mut diags) = resolve::resolve_program(&program);

    // Pass 1: lower top-level signatures (functions, structs, enum variants,
    // top-level lets, function params). Continues even when `diags` already
    // contains resolve errors — `lower_type`'s `Ty::Error` sentinel
    // suppresses cascading diagnostics from sub-trees that failed earlier.
    let (mut def_types, struct_fields, variant_payloads) = signature_pass(
        &program,
        &resolutions,
        &definitions,
        &binding_def_ids,
        &mut diags,
    );

    // Pass 2: bidirectional type checking of function bodies and top-level
    // let init expressions. Task 4 lands literal/ident/operator rules; later
    // tasks extend Pass 2 to calls / struct literals / control flow / match.
    let (types, type_diags) = check::run(
        &program,
        &resolutions,
        &definitions,
        &binding_def_ids,
        &mut def_types,
        &struct_fields,
        &variant_payloads,
    );
    diags.extend(type_diags);

    if !diags.is_empty() {
        return Err(diags);
    }
    Ok(TypedProgram {
        program,
        types,
        resolutions,
        definitions,
        binding_def_ids,
        def_types,
        struct_fields,
        variant_payloads,
    })
}

/// Walks each top-level item, lowering its declared types into the per-
/// definition tables. Function param DefIds get their types here so Pass 2
/// (function body walks) can read them. Top-level `Item::Let` gets its
/// declared type recorded; the init expression is type-checked in Pass 2.
fn signature_pass(
    program: &Program,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    binding_def_ids: &BindingTable,
    diags: &mut Vec<Diagnostic>,
) -> (DefTypeMap, StructFieldMap, VariantPayloadMap) {
    let mut def_types: DefTypeMap = HashMap::new();
    let mut struct_fields: StructFieldMap = HashMap::new();
    let mut variant_payloads: VariantPayloadMap = HashMap::new();
    // Outer-enum first-writer-wins gate. The resolver maps duplicate enum
    // names to the FIRST occurrence's DefId via `name_to_def`; without this
    // set, the second `enum E { ... }` would re-process the same enum_def_id
    // and overwrite variant signatures (e.g. with the wrong payload list).
    // Tracking processed enum DefIds here is the analogue of the existing
    // `def_types.contains_key` / `struct_fields.contains_key` gates for
    // functions/structs.
    let mut enums_lowered: std::collections::HashSet<DefId> = std::collections::HashSet::new();

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
                // First-writer-wins: when two top-level items share a name,
                // the resolver emits `duplicate_name` and re-uses the first
                // DefId. Skipping the second's lowering keeps `def_types`
                // consistent with the first body's declared signature and
                // avoids spurious cascade diagnostics — e.g. without this
                // gate, `function f(): Int return 0 end` followed by
                // `function f(): Bool return true end` would type-check
                // the FIRST body against `Bool`. The gate sits before
                // `lower_type` so a duplicate's invalid annotation does
                // not fire redundant diagnostics either.
                if def_types.contains_key(&def_id) {
                    continue;
                }
                let param_tys: Vec<Ty> = f
                    .params
                    .iter()
                    .map(|p| lower_type(&p.ty, resolutions, definitions, diags))
                    .collect();
                let ret_ty = lower_type(&f.return_ty, resolutions, definitions, diags);
                // Param DefIds aren't in `name_to_def` (function-scoped, not
                // hoisted). Look each up by its AST NodeId via
                // `binding_def_ids` (populated by the resolver when the
                // param was introduced). O(params), no scan over
                // `DefinitionTable`.
                for (p, ty) in f.params.iter().zip(param_tys.iter()) {
                    let Some(p_def_id) = binding_def_ids.get(&p.id).copied() else {
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
                // First-writer-wins (see Item::Function arm). `struct_fields`
                // is the canonical "is this struct already lowered" probe.
                if struct_fields.contains_key(&def_id) {
                    continue;
                }
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
                // Outer-enum first-writer-wins. The resolver re-uses the
                // first definition's DefId on duplicates, so without this
                // gate the second `enum E { ... }`'s variant list would
                // overwrite the first's. Closes the cross-task review's
                // "outer-enum gate missing" finding.
                if !enums_lowered.insert(enum_def_id) {
                    continue;
                }

                // Substitution map from this enum's type-parameter names to
                // schema indices (e.g. `T → 0`, `E → 1` for
                // `enum Result<T, E>`). Empty for non-generic enums; in
                // that case `lower_type_with_subst` reduces to `lower_type`.
                let type_param_subst: ParamSubst<'_> = e
                    .type_params
                    .iter()
                    .enumerate()
                    .map(|(i, name)| (name.as_str(), i))
                    .collect();
                let return_args: Vec<Ty> = (0..e.type_params.len()).map(Ty::Param).collect();
                let return_ty = Ty::Enum(enum_def_id, return_args);

                for variant in &e.variants {
                    let Some(variant_def_id) = name_to_def.get(variant.name.as_str()).copied()
                    else {
                        continue;
                    };
                    // Per-variant gate: two enums with colliding variant
                    // names would otherwise overwrite each other's payload
                    // entries. Redundant once the outer-enum gate fires
                    // for the duplicate, but cheap and explicit.
                    if variant_payloads.contains_key(&variant_def_id) {
                        continue;
                    }
                    let payload: Vec<Ty> = variant
                        .payload
                        .iter()
                        .map(|t| {
                            lower_type_with_subst(
                                t,
                                resolutions,
                                definitions,
                                &type_param_subst,
                                diags,
                            )
                        })
                        .collect();
                    variant_payloads.insert(
                        variant_def_id,
                        VariantPayload {
                            parent_enum: enum_def_id,
                            payload: payload.clone(),
                        },
                    );
                    // Variant constructor schema. Differentiate by arity so
                    // the use-site retrieval (Task 4) can instantiate Param
                    // → Var without per-shape unwrapping:
                    //   - Variants WITH payload: `Function(payload, Enum)` —
                    //     called as `Some(x)`; synth_call resolves the Vars
                    //     against the arg's type.
                    //   - Nullary variants: bare `Enum(parent, [Param...])`
                    //     — used as a value (`None`); checked-expr context
                    //     resolves the Var against the expected enum type.
                    // Task 4's synth_ident treats both shapes uniformly via
                    // a single `instantiate_schema` walk.
                    let schema = if payload.is_empty() {
                        return_ty.clone()
                    } else {
                        Ty::Function(payload, Box::new(return_ty.clone()))
                    };
                    def_types.insert(variant_def_id, schema);
                }
            }
            Item::Let(l) => {
                let Some(def_id) = name_to_def.get(l.name.as_str()).copied() else {
                    continue;
                };
                // First-writer-wins (see Item::Function arm).
                if def_types.contains_key(&def_id) {
                    continue;
                }
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

    // ----- PR-3c Task 3: variant signature schemas -----

    #[test]
    fn signature_pass_populates_generic_variant_with_param() {
        // `Just(T)` inside `enum Maybe<T>` lowers to
        // `Function([Param(0)], Enum(maybe_def, [Param(0)]))`. The
        // generic-instantiation site (Task 4) substitutes Param→Var.
        let prog = parse_src("enum Maybe<T>\n  Just(T)\n  Nothing\nend");
        let typed = check(prog).unwrap();

        let just_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Just")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&just_def).cloned().unwrap();
        let Ty::Function(params, ret) = sig else {
            panic!("expected Ty::Function, got {sig:?}");
        };
        assert_eq!(params, vec![Ty::Param(0)]);
        let Ty::Enum(_, args) = *ret else {
            panic!("expected Ty::Enum return");
        };
        assert_eq!(args, vec![Ty::Param(0)]);

        // The nullary `Nothing` variant: stored as bare
        // `Enum(maybe_def, [Param(0)])` — no `Function` wrapper. Use sites
        // (Task 4) instantiate Param → fresh Var directly. The bare-Enum
        // shape lets nullary variants flow as values without callers
        // having to special-case `Function([], _)` unwrapping.
        let nothing_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Nothing")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&nothing_def).cloned().unwrap();
        let Ty::Enum(_, args) = sig else {
            panic!("expected bare Ty::Enum for nullary, got {sig:?}");
        };
        assert_eq!(args, vec![Ty::Param(0)]);
    }

    #[test]
    fn signature_pass_populates_two_param_enum() {
        // `enum Result<T, E>`: Ok(T) → Param(0), Err(E) → Param(1).
        let prog = parse_src("enum Result<T, E>\n  Ok(T)\n  Err(E)\nend");
        let typed = check(prog).unwrap();

        let ok_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Ok")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&ok_def).cloned().unwrap();
        let Ty::Function(params, ret) = sig else {
            panic!("expected Ty::Function for Ok");
        };
        assert_eq!(params, vec![Ty::Param(0)]);
        let Ty::Enum(_, args) = *ret else {
            panic!("expected Ty::Enum return for Ok");
        };
        assert_eq!(args, vec![Ty::Param(0), Ty::Param(1)]);

        let err_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Err")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&err_def).cloned().unwrap();
        let Ty::Function(params, ret) = sig else {
            panic!("expected Ty::Function for Err");
        };
        assert_eq!(params, vec![Ty::Param(1)]);
        let Ty::Enum(_, args) = *ret else {
            panic!("expected Ty::Enum return for Err");
        };
        assert_eq!(args, vec![Ty::Param(0), Ty::Param(1)]);
    }

    #[test]
    fn signature_pass_populates_non_generic_variant_signature() {
        // Non-generic enums: type_params empty, payload uses concrete
        // types, return is `Enum(_, [])`. Closes PR-3b's silent gap where
        // even non-generic variants had no `def_types` entry.
        let prog = parse_src("enum Maybe\n  Just(Int)\n  Nothing\nend");
        let typed = check(prog).unwrap();

        let just_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Just")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&just_def).cloned().unwrap();
        let Ty::Function(params, ret) = sig else {
            panic!("expected Ty::Function for Just");
        };
        assert_eq!(params, vec![Ty::Int]);
        let Ty::Enum(_, args) = *ret else {
            panic!("expected Ty::Enum return for Just");
        };
        assert!(args.is_empty(), "non-generic enum has no Param args");

        let nothing_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Nothing")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&nothing_def).cloned().unwrap();
        // Non-generic + nullary: bare `Enum(_, [])`.
        let Ty::Enum(_, args) = sig else {
            panic!("expected bare Ty::Enum for non-generic nullary, got {sig:?}");
        };
        assert!(args.is_empty());
    }

    #[test]
    fn signature_pass_outer_enum_first_writer_wins() {
        // Pin the `enums_lowered` outer-enum gate (sema.rs ~227) by
        // inspecting `variant_payloads` directly after `signature_pass`
        // runs. The previous version of this test only asserted
        // `diags.len() == 1`, which the resolver's `duplicate_name`
        // diagnostic satisfies on its own — so the test would still
        // pass even if the gate were removed (false-positive guard).
        //
        // Calling `check()` here is unsuitable because it returns
        // `Err(diags)` when any diagnostic exists, leaving no handle on
        // the partial tables. We invoke the resolver and
        // `signature_pass` directly so the gate's *effect* on the
        // payload map is observable.
        //
        // Expected gate behavior:
        //   - The FIRST enum's variant `A` is in `variant_payloads`.
        //   - The SECOND enum's variant `B` is NOT in `variant_payloads`
        //     — `enums_lowered.insert` returns false on the duplicate
        //     parent DefId, so the inner variant loop is skipped
        //     entirely.
        //   - `signature_pass` adds zero cascade diagnostics on top of
        //     the resolver's single `duplicate_name`.
        let prog = parse_src("enum E\n  A\nend\nenum E\n  B\nend");
        let (resolutions, definitions, binding_def_ids, mut diags) =
            resolve::resolve_program(&prog);
        let resolver_diag_count = diags.len();
        assert_eq!(
            resolver_diag_count, 1,
            "resolver should fire exactly one duplicate-name diag, got: {:?}",
            diags
        );
        assert!(
            diags[0].message.contains("already defined") || diags[0].message.contains("duplicate"),
            "resolver diag msg: {}",
            diags[0].message
        );

        let (_def_types, _struct_fields, variant_payloads) = signature_pass(
            &prog,
            &resolutions,
            &definitions,
            &binding_def_ids,
            &mut diags,
        );

        // No-cascade: signature_pass must not push additional diags on
        // top of the resolver's report.
        assert_eq!(
            diags.len(),
            resolver_diag_count,
            "signature_pass added {} cascade diag(s) over the resolver's: {:?}",
            diags.len() - resolver_diag_count,
            diags
        );

        // First enum's variant A has a payload entry.
        let a_def = definitions
            .iter()
            .find(|(_, info)| info.name == "A" && matches!(info.kind, DefKind::EnumVariant))
            .map(|(id, _)| *id)
            .expect("first enum's variant A must have a DefId");
        assert!(
            variant_payloads.contains_key(&a_def),
            "first enum's variant A must be lowered into variant_payloads"
        );

        // Second enum's variant B (if the resolver gave it a distinct
        // DefId) must NOT have a payload entry — that is precisely what
        // the outer-enum gate guarantees. If the gate were removed,
        // signature_pass would re-process the duplicate enum's body and
        // insert B under the FIRST enum's parent DefId, corrupting the
        // first-writer-wins invariant.
        let b_def = definitions
            .iter()
            .find(|(_, info)| info.name == "B" && matches!(info.kind, DefKind::EnumVariant))
            .map(|(id, _)| *id)
            .expect(
                "second enum's variant B must have a DefId — without one, this test cannot \
                 distinguish gate-on from gate-off",
            );
        assert!(
            !variant_payloads.contains_key(&b_def),
            "outer-enum gate must skip the duplicate enum's body — \
             variant B should NOT appear in variant_payloads"
        );
    }

    #[test]
    fn signature_pass_nested_generic_payload() {
        // `Wrap(Result<T, String>)` — the outer payload is a generic enum
        // instantiation: `T` substitutes to `Param(0)` (from
        // `WrappedResult<T>`'s scope), `String` lowers concretely.
        let prog = parse_src(
            "enum Result<T, E>\n  Ok(T)\n  Err(E)\nend\nenum WrappedResult<T>\n  Wrap(Result<T, String>)\nend",
        );
        let typed = check(prog).unwrap();

        let wrap_def = typed
            .definitions
            .iter()
            .find(|(_, info)| info.name == "Wrap")
            .map(|(id, _)| *id)
            .unwrap();
        let sig = typed.def_types.get(&wrap_def).cloned().unwrap();
        let Ty::Function(params, _) = sig else {
            panic!("expected Ty::Function for Wrap");
        };
        let [Ty::Enum(_, inner_args)] = params.as_slice() else {
            panic!("expected nested Ty::Enum payload, got {params:?}");
        };
        assert_eq!(inner_args.len(), 2);
        assert_eq!(inner_args[0], Ty::Param(0));
        assert_eq!(inner_args[1], Ty::String);
    }

    #[test]
    fn signature_pass_preserves_struct_and_let_handling() {
        // Negative regression: adding generic-enum logic must not break
        // struct/let handling.
        let prog = parse_src("struct P\n  x: Int\nend\nlet pi: Scalar = 3.14");
        let typed = check(prog).unwrap();
        assert!(!typed.struct_fields.is_empty());
        assert!(!typed.def_types.is_empty());
    }
}
