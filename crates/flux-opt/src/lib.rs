#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

mod call_graph;

use std::collections::VecDeque;

use flux_middle::{
    PanicReason, PanicSpec,
    call_graph::{CallGraph, CallSite, CallSiteKind, Node, NodeKey},
    global_env::GlobalEnv,
    queries::Providers,
};
use rustc_data_structures::unord::UnordMap;
use rustc_span::Span;

pub fn provide(providers: &mut Providers) {
    providers.call_graph = call_graph::build_call_graph;
    providers.inferred_no_panic = inferred_no_panic;
}

/// Implements a greatest fixpoint on the two-point lattice `WillNotPanic` > `MightPanic(_)`:
/// 1. Seed every node optimistically (`WillNotPanic` for fully-resolved `Analyzed` nodes).
/// 2. Add all `MightPanic` seeds to a worklist.
/// 3. Propagate pessimism upward: when a node is `MightPanic`, mark each `WillNotPanic`
///    caller as `MightPanic(Transitive)` and enqueue it.
///
/// Each node flips at most once, so the loop terminates. Cycles with no reachable panic
/// source correctly remain `WillNotPanic`.
///
/// `external_spec` resolves the spec of an `Instance` defined in another crate (a
/// [`Node::ExternalCrate`]), looking it up in that crate's serialized metadata.
pub fn inferred_no_panic<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
) -> UnordMap<NodeKey<'tcx>, PanicSpec<'tcx>> {
    let graph = genv.call_graph();

    let mut specs: UnordMap<NodeKey<'tcx>, PanicSpec<'tcx>> = UnordMap::default();
    let mut queue: VecDeque<NodeKey<'tcx>> = VecDeque::new();

    for (&key, node) in &graph.nodes {
        let spec = initial_spec(genv, node, key);
        if matches!(spec, PanicSpec::MightPanic(_)) {
            queue.push_back(key);
        }
        specs.insert(key, spec);
    }

    while let Some(key) = queue.pop_front() {
        let Some(callers) = graph.callers.get(&key) else { continue };
        for &caller in callers {
            if specs[&caller] == PanicSpec::WillNotPanic {
                let call_site = call_site_span_to(&graph, caller, key);
                specs.insert(
                    caller,
                    PanicSpec::MightPanic(PanicReason::Transitive { callee: key, call_site }),
                );
                queue.push_back(caller);
            }
        }
    }
    specs
}

/// Computes the initial `PanicSpec` for a node before propagation.
///
/// `Analyzed` nodes with only resolved call sites and no explicit panics start as `WillNotPanic`
/// (optimistic). Every other node starts as `MightPanic` with the appropriate reason.
fn initial_spec<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
    node: &Node<'tcx>,
    key: NodeKey<'tcx>,
) -> PanicSpec<'tcx> {
    match node {
        Node::ExternalCrate => genv.inferred_no_panic_external(key),
        Node::Leaf(_) => PanicSpec::MightPanic(PanicReason::NoMIRAvailable),
        Node::Analyzed { call_sites } => {
            for site in call_sites {
                let reason = match site.kind {
                    CallSiteKind::SynthesizedPanic => {
                        PanicReason::SynthesizedPanic { call_site: site.span }
                    }
                    CallSiteKind::DynamicDispatch => {
                        PanicReason::DynamicDispatch { call_site: site.span }
                    }
                    CallSiteKind::Unresolved { def_id } => {
                        PanicReason::UnresolvedCall { def_id, call_site: site.span }
                    }
                    CallSiteKind::Resolved { .. } => continue,
                };
                return PanicSpec::MightPanic(reason);
            }
            PanicSpec::WillNotPanic
        }
    }
}

/// Returns the span of the first call site in `caller`'s body that resolves to `callee`.
///
/// By graph construction, if `caller` appears in `graph.callers[callee]`, a matching resolved
/// site must exist. Falls back to `DUMMY_SP` only if the graph is somehow inconsistent.
fn call_site_span_to<'tcx>(
    graph: &CallGraph<'tcx>,
    caller: NodeKey<'tcx>,
    callee: NodeKey<'tcx>,
) -> Span {
    graph
        .nodes
        .get(&caller)
        .and_then(|n| {
            n.call_sites().iter().find_map(|s: &CallSite<'tcx>| {
                matches!(s.kind, CallSiteKind::Resolved { callee: c } if c == callee)
                    .then_some(s.span)
            })
        })
        .unwrap_or(rustc_span::DUMMY_SP)
}
