//! Match exhaustiveness checker.
//!
//! Per /design-discussion 2026-05-08 (Q3 I-extended), uses per-scrutinee
//! table-driven dispatch with 1-level payload recursion. Each `Ty` kind
//! has a coverage rule; new scrutinee kinds plug in by adding a match
//! arm. Maranget-style arbitrary-depth nesting is deferred — the
//! 1-level rule catches the common `case Some(Some(x))` /
//! `case Some(None)` gap and is sufficient for the current spec; a
//! future replacement is an internal-only swap of this module.
//!
//! ## Coverage rules
//!
//! - `Enum`: every variant must be covered by a variant pattern (or a
//!   catch-all `_` / Ident binding satisfies all).
//! - `Bool`: `true` and `false` both required (catch-all satisfies).
//! - `Int` / `Scalar` / `String` / `Vec` / `Mat` / `Array` / `Dict`: a
//!   catch-all is required — these types don't have a finite canonical
//!   pattern set, so individual literal patterns can never be exhaustive
//!   on their own.
//! - `Struct`: single shape, always exhaustive (any catch-all suffices;
//!   destructuring patterns aren't yet a surface feature).
//! - `Function`: not matchable — function values have no equality, so
//!   matching them is always nonsensical.
//! - `Var` / `Param` / `Error`: skip (no-cascade — earlier passes
//!   already pinned the issue or these are internal sentinels).
//!
//! ## 1-level payload recursion
//!
//! For `Enum` scrutinees, after top-level coverage we examine each
//! covered variant's payload columns. For each column, we gather the
//! sub-patterns at that position across all matching arms and recur
//! once with `recurse=false` so deeper nesting falls back to flat
//! coverage. This catches `Option<Option<Int>>` cases like
//! `case Some(Some(x)); case None` (missing inner `Some(None)`).

use std::collections::{HashMap, HashSet};

use crate::ast::{MatchArm, Pattern, PatternKind};
use crate::diag::Diagnostic;
use crate::ids::DefId;
use crate::sema::VariantPayloadMap;
use crate::sema::resolve::{DefinitionTable, ResolveTable};
use crate::sema::ty::Ty;
use crate::source::Span;

pub(crate) fn check_exhaustive(
    scrut_ty: &Ty,
    arms: &[MatchArm],
    span: Span,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    variant_payloads: &VariantPayloadMap,
) -> Vec<Diagnostic> {
    let patterns: Vec<&Pattern> = arms.iter().map(|a| &a.pattern).collect();
    check_patterns(
        scrut_ty,
        &patterns,
        span,
        resolutions,
        definitions,
        variant_payloads,
        true,
    )
}

fn check_patterns(
    scrut_ty: &Ty,
    patterns: &[&Pattern],
    span: Span,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    variant_payloads: &VariantPayloadMap,
    recurse_payload: bool,
) -> Vec<Diagnostic> {
    match scrut_ty {
        Ty::Enum(def_id, type_args) => check_enum_coverage(
            *def_id,
            type_args,
            patterns,
            span,
            resolutions,
            definitions,
            variant_payloads,
            recurse_payload,
        ),
        Ty::Bool => check_bool_coverage(patterns, span),
        Ty::Int | Ty::Scalar(_) | Ty::String => {
            require_catchall(patterns, span, kind_name(scrut_ty))
        }
        Ty::Vec(_, _) | Ty::Mat(_, _) | Ty::Array(_) | Ty::Dict(_, _) => {
            require_catchall(patterns, span, kind_name(scrut_ty))
        }
        Ty::Struct(_) => Vec::new(), // single shape; any pattern suffices
        Ty::Function(_, _) => vec![Diagnostic::type_error(
            span,
            "match on function value is not allowed".to_string(),
        )],
        // Sentinels: skip exhaustiveness checking. `Var`/`Param` mean an
        // earlier inference pass didn't pin the scrutinee; `Error`
        // means upstream already fired a diag — no-cascade.
        Ty::Var(_) | Ty::Param(_) | Ty::Error => Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn check_enum_coverage(
    def_id: DefId,
    type_args: &[Ty],
    patterns: &[&Pattern],
    span: Span,
    resolutions: &ResolveTable,
    definitions: &DefinitionTable,
    variant_payloads: &VariantPayloadMap,
    recurse_payload: bool,
) -> Vec<Diagnostic> {
    // Collect all variant DefIds belonging to this enum (used to
    // recognize bare nullary variant patterns parsed as `Ident`).
    let all_variants: Vec<DefId> = variant_payloads
        .iter()
        .filter_map(|(vid, info)| (info.parent_enum == def_id).then_some(*vid))
        .collect();

    // Walk patterns once, classifying each:
    //   - `Wildcard` → top-level catch-all, covers everything.
    //   - `Ident(name)` whose `name` matches a variant of this enum →
    //     treated as a nullary variant pattern (the parser doesn't
    //     distinguish these from bindings since dyne's `case Nothing`
    //     elides parens; the resolver still records it as a binding,
    //     but for coverage we credit the variant).
    //   - `Ident(name)` not matching any variant → catch-all binding.
    //   - `Variant(_, sub_patterns)` resolving to a variant of this
    //     enum → covers that variant; sub_patterns feed 1-level
    //     payload recursion. Variants resolving to a different parent
    //     are silently skipped (Task 5's `wrong_variant_for_enum`
    //     already pinned the type error).
    //   - Other patterns (literals) → not relevant for enum coverage.
    // `variant_arm_sub_patterns[variant_def]` is one entry per matching
    // arm, each entry being that arm's payload sub-patterns. We index by
    // column later for 1-level recursion: column N gathers each arm's
    // sub-pattern at position N. Flattening across arms would lose that
    // structure for multi-arity variants.
    let mut covered_variants: HashSet<DefId> = HashSet::new();
    let mut variant_arm_sub_patterns: HashMap<DefId, Vec<&Vec<Pattern>>> = HashMap::new();
    for p in patterns {
        match &p.kind {
            PatternKind::Wildcard => return Vec::new(),
            PatternKind::Ident(name) => {
                if let Some(variant_def) = variant_def_by_name(name, &all_variants, definitions) {
                    covered_variants.insert(variant_def);
                } else {
                    // Catch-all binding; no missing variants.
                    return Vec::new();
                }
            }
            PatternKind::Variant(_, sub_patterns) => {
                let Some(variant_def) = resolutions.get(&p.id).copied() else {
                    continue;
                };
                let Some(payload_info) = variant_payloads.get(&variant_def) else {
                    continue;
                };
                if payload_info.parent_enum != def_id {
                    continue;
                }
                covered_variants.insert(variant_def);
                variant_arm_sub_patterns
                    .entry(variant_def)
                    .or_default()
                    .push(sub_patterns);
            }
            PatternKind::IntLit(_) | PatternKind::BoolLit(_) | PatternKind::StrLit(_) => {}
        }
    }

    let mut diags = Vec::new();

    // Top-level missing variants — list in declaration order so the
    // message reads naturally.
    let missing: Vec<&str> = all_variants
        .iter()
        .filter(|vid| !covered_variants.contains(vid))
        .filter_map(|vid| definitions.get(vid).map(|info| info.name.as_str()))
        .collect();
    if !missing.is_empty() {
        diags.push(crate::sema::diag::non_exhaustive_enum(span, &missing));
    }

    // 1-level payload recursion. Skip on the inner call
    // (`recurse_payload=false`) so deeper nesting falls back to flat
    // coverage at the enclosing level — Maranget-style arbitrary
    // nesting is a future swap.
    if recurse_payload {
        for (variant_def, arms_sub_patterns) in &variant_arm_sub_patterns {
            let Some(payload_info) = variant_payloads.get(variant_def) else {
                continue;
            };
            // Substitute Param(i) → type_args[i] so the inner recursion
            // sees the concrete payload type instead of the variant
            // schema's bare `Param`.
            let substituted: Vec<Ty> = payload_info
                .payload
                .iter()
                .map(|t| t.subst_with_args(type_args))
                .collect();
            // For each payload column, gather one sub-pattern per arm
            // at that column and check exhaustiveness recursively.
            // Arity-mismatched arms (Task 5 already diagnosed) contribute
            // no pattern at out-of-range columns and are silently
            // skipped — the structural error has been pinned upstream.
            for (col, sub_ty) in substituted.iter().enumerate() {
                let column_patterns: Vec<&Pattern> = arms_sub_patterns
                    .iter()
                    .filter_map(|arm_subs| arm_subs.get(col))
                    .collect();
                if column_patterns.is_empty() {
                    continue;
                }
                diags.extend(check_patterns(
                    sub_ty,
                    &column_patterns,
                    span,
                    resolutions,
                    definitions,
                    variant_payloads,
                    false,
                ));
            }
        }
    }

    diags
}

fn check_bool_coverage(patterns: &[&Pattern], span: Span) -> Vec<Diagnostic> {
    if has_catchall(patterns) {
        return Vec::new();
    }
    let mut seen_true = false;
    let mut seen_false = false;
    for p in patterns {
        if let PatternKind::BoolLit(b) = &p.kind {
            if *b {
                seen_true = true;
            } else {
                seen_false = true;
            }
        }
    }
    let mut missing: Vec<&str> = Vec::new();
    if !seen_true {
        missing.push("true");
    }
    if !seen_false {
        missing.push("false");
    }
    if missing.is_empty() {
        Vec::new()
    } else {
        vec![crate::sema::diag::non_exhaustive_bool(span, &missing)]
    }
}

fn require_catchall(patterns: &[&Pattern], span: Span, kind: &str) -> Vec<Diagnostic> {
    if has_catchall(patterns) {
        Vec::new()
    } else {
        vec![crate::sema::diag::requires_wildcard(span, kind)]
    }
}

/// Catch-all detection for non-Enum scrutinees: a top-level `_`
/// (Wildcard) or any `Ident` binding covers every value. Enum coverage
/// has its own walker that disambiguates `Ident("Variant")` from a
/// bare binding by looking up the name in the enum's variants.
fn has_catchall(patterns: &[&Pattern]) -> bool {
    patterns
        .iter()
        .any(|p| matches!(p.kind, PatternKind::Wildcard | PatternKind::Ident(_)))
}

/// Return the variant DefId in `all_variants` whose name matches `name`,
/// or `None` if none does. Used by `check_enum_coverage` to recognize
/// bare nullary variant patterns (parsed as `Ident` because dyne syntax
/// elides parens for nullary variants).
fn variant_def_by_name(
    name: &str,
    all_variants: &[DefId],
    definitions: &DefinitionTable,
) -> Option<DefId> {
    all_variants
        .iter()
        .find(|vid| definitions.get(vid).is_some_and(|info| info.name == name))
        .copied()
}

fn kind_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::Int => "Int",
        Ty::Scalar(_) => "Scalar",
        Ty::String => "String",
        Ty::Vec(_, _) => "Vec",
        Ty::Mat(_, _) => "Mat",
        Ty::Array(_) => "Array",
        Ty::Dict(_, _) => "Dict",
        _ => "type",
    }
}
