#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

mod call_graph;

use std::collections::VecDeque;

use call_graph::{CallGraph, CallSiteKind, NodeKind};
use flux_middle::{
    CannotResolveReason, PanicReason, PanicSpec, global_env::GlobalEnv, queries::Providers,
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Instance;

pub fn provide(providers: &mut Providers) {
    providers.inferred_no_panic = inferred_no_panic;
}

pub fn inferred_no_panic(genv: GlobalEnv) -> FxHashMap<DefId, PanicSpec> {
    infer_no_panics(genv, |def_id| genv.inferred_no_panic(def_id))
}

/// The entry point for no-panic inference. Given a root function, explores its
/// call graph and returns an over-approximation of whether it might panic.
pub fn infer_no_panics(
    genv: GlobalEnv,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    let graph = call_graph::build_call_graph(genv);
    run_fixpoint(&graph, external_spec)
}

// ---- Fixpoint phase ---------------------------------------------------------

/// Consumes the labeled call graph and produces a `PanicSpec` for every root node.
///
/// Seeding is explicit per `NodeKind`:
/// - `ExternalCrate` → looked up via `external_spec`
/// - `Opaque`        → `WillNotPanic` (compiler-generated glue, conservatively safe)
/// - `NoBody` / `MIRUnavailable` → `MightPanic(CannotResolve(...))`
/// - `Analyzed` with unresolvable call sites → `MightPanic(CannotResolve(...))` (final)
/// - `Analyzed` with no unresolvable calls → `MightPanic(Unknown)`, resolved by fixpoint
fn run_fixpoint(
    graph: &CallGraph<'_>,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    // --- Seeding ---
    let mut specs: FxHashMap<Instance<'_>, PanicSpec> = FxHashMap::default();

    for (&instance, node) in &graph.nodes {
        let def_id = instance.def_id();
        let spec = match &node.kind {
            NodeKind::ExternalCrate => external_spec(def_id),
            NodeKind::Leaf(def_kind) => {
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::NoMIRAvailable(def_id, *def_kind),
                ))
            }
            NodeKind::Analyzed { .. } if node.call_sites.is_empty() => PanicSpec::WillNotPanic,
            NodeKind::Analyzed { .. } => {
                // If any call site is statically unresolvable, the function is
                // immediately MightPanic(CannotResolve). Otherwise start as Unknown
                // for the fixpoint to resolve.
                let unresolvable = node.call_sites.iter().find(|site| {
                    matches!(
                        site.kind,
                        CallSiteKind::DynamicDispatch | CallSiteKind::Unresolved { .. }
                    )
                });
                if let Some(site) = unresolvable {
                    let reason = match site.kind {
                        CallSiteKind::DynamicDispatch => CannotResolveReason::NotFnDef(def_id),
                        CallSiteKind::Unresolved { def_id: method } => {
                            CannotResolveReason::UnresolvedTraitMethod(method)
                        }
                        _ => unreachable!(),
                    };
                    PanicSpec::MightPanic(PanicReason::CannotResolve(reason))
                } else {
                    PanicSpec::MightPanic(PanicReason::Unknown)
                }
            }
        };
        specs.insert(instance, spec);
    }

    // --- Fixpoint iteration (workqueue) ---
    let mut queue: VecDeque<Instance<'_>> = specs
        .iter()
        .filter_map(|(&inst, spec)| {
            matches!(spec, PanicSpec::MightPanic(PanicReason::Unknown)).then_some(inst)
        })
        .collect();

    while let Some(instance) = queue.pop_front() {
        let current_spec = specs.get(&instance).unwrap();

        // WillNotPanic, CannotResolve, and Transitive are all final states.
        match current_spec {
            PanicSpec::WillNotPanic
            | PanicSpec::MightPanic(PanicReason::CannotResolve(_))
            | PanicSpec::MightPanic(PanicReason::Transitive) => continue,
            _ => {}
        }

        let call_sites = &graph.nodes[&instance].call_sites;

        let mut has_definitively_bad = false;
        let mut has_unresolved = false;

        for site in call_sites {
            match site.kind {
                CallSiteKind::Resolved { callee } => {
                    match specs.get(&callee) {
                        Some(PanicSpec::WillNotPanic) => {}
                        Some(PanicSpec::MightPanic(PanicReason::Unknown)) => {
                            has_unresolved = true;
                        }
                        _ => {
                            has_definitively_bad = true;
                        }
                    }
                }
                // DynamicDispatch and UnresolvedTrait are handled at seeding time.
                CallSiteKind::SynthesizedPanic
                | CallSiteKind::DynamicDispatch
                | CallSiteKind::Unresolved { .. } => {}
            }
        }

        let new_spec = if has_definitively_bad {
            PanicSpec::MightPanic(PanicReason::Transitive)
        } else if !has_unresolved {
            PanicSpec::WillNotPanic
        } else {
            continue;
        };

        specs.insert(instance, new_spec);

        if let Some(callers) = graph.callers.get(&instance) {
            queue.extend(callers.iter().copied());
        }
    }

    // Filter to real nodes only, mapping back to DefId.
    graph
        .nodes
        .iter()
        .filter_map(|(&instance, node)| {
            match &node.kind {
                NodeKind::Analyzed { is_mono: false } => {
                    Some((instance.def_id(), specs[&instance].clone()))
                }
                _ => None,
            }
        })
        .collect()
}
