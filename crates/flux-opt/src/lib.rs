#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;

mod call_graph;

use std::collections::VecDeque;

use flux_middle::{
    PanicReason, PanicSpec,
    call_graph::{CallGraph, CallSiteKind, Node},
    global_env::GlobalEnv,
    queries::Providers,
};
use rustc_data_structures::unord::UnordMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Instance;

pub fn provide(providers: &mut Providers) {
    providers.call_graph = call_graph::build_call_graph;
    providers.inferred_no_panic = inferred_no_panic;
}

pub fn inferred_no_panic<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
) -> UnordMap<Instance<'tcx>, PanicSpec> {
    infer_no_panics(genv, |def_id| genv.inferred_no_panic(def_id))
}

/// The entry point for no-panic inference. Explores the call graph and returns, for every analyzed
/// `Instance`, an over-approximation of whether it might panic.
pub fn infer_no_panics<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> UnordMap<Instance<'tcx>, PanicSpec> {
    let graph = genv.call_graph();
    run_fixpoint(graph, external_spec)
}

/// Computes the initial `PanicSpec` for a node before propagation.
///
/// `Analyzed` nodes with only resolved call sites start as `WillNotPanic` (optimistic).
/// Every other node starts as `MightPanic` with the appropriate reason.
fn initial_spec(
    node: &Node<'_>,
    external_spec: &impl Fn(DefId) -> PanicSpec,
    def_id: DefId,
) -> PanicSpec {
    match node {
        Node::ExternalCrate => external_spec(def_id),
        Node::Leaf(_) => PanicSpec::MightPanic(PanicReason::NoMIRAvailable),
        Node::Analyzed { call_sites, .. } => {
            for site in call_sites {
                let reason = match site.kind {
                    CallSiteKind::SynthesizedPanic => PanicReason::SynthesizedPanic,
                    CallSiteKind::DynamicDispatch => PanicReason::DynamicDispatch,
                    CallSiteKind::Unresolved { def_id } => PanicReason::UnresolvedCall(def_id),
                    CallSiteKind::Resolved { .. } => continue,
                };
                return PanicSpec::MightPanic(reason);
            }
            PanicSpec::WillNotPanic
        }
    }
}

/// Consumes the labeled call graph and produces a `PanicSpec` for every root node.
///
/// Implements a greatest fixpoint on the two-point lattice `WillNotPanic` > `MightPanic(_)`:
/// 1. Seed every node optimistically (`WillNotPanic` for fully-resolved `Analyzed` nodes).
/// 2. Add all `MightPanic` seeds to a worklist.
/// 3. Propagate pessimism upward: when a node is `MightPanic`, mark each `WillNotPanic`
///    caller as `MightPanic(Transitive)` and enqueue it.
///
/// Each node flips at most once, so the loop terminates. Cycles with no reachable panic
/// source correctly remain `WillNotPanic`.
fn run_fixpoint<'tcx>(
    graph: &CallGraph<'tcx>,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> UnordMap<Instance<'tcx>, PanicSpec> {
    let mut specs: FxHashMap<Instance<'tcx>, PanicSpec> = FxHashMap::default();
    let mut queue: VecDeque<Instance<'tcx>> = VecDeque::new();

    for (&instance, node) in &graph.nodes {
        let spec = initial_spec(node, &external_spec, instance.def_id());
        if matches!(spec, PanicSpec::MightPanic(_)) {
            queue.push_back(instance);
        }
        specs.insert(instance, spec);
    }

    while let Some(instance) = queue.pop_front() {
        let Some(callers) = graph.callers.get(&instance) else { continue };
        for &caller in callers {
            if specs[&caller] == PanicSpec::WillNotPanic {
                specs.insert(caller, PanicSpec::MightPanic(PanicReason::Transitive));
                queue.push_back(caller);
            }
        }
    }

    // Return every analyzed instance's spec, keyed by `Instance`. The `DefId`-keyed projection
    // (identity instances only) now happens downstream in `Queries::inferred_no_panic_crate` for
    // the metadata/checker path; it is removed entirely once the checker queries by `Instance`.
    specs.into_iter().collect()
}
