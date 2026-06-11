#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;

mod call_graph;

use std::collections::VecDeque;

use flux_middle::{
    PanicReason, PanicSpec,
    call_graph::{CallSiteKind, Node},
    global_env::GlobalEnv,
    queries::Providers,
};
use rustc_data_structures::unord::UnordMap;
use rustc_middle::ty::Instance;

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
pub fn inferred_no_panic<'tcx>(genv: GlobalEnv<'_, 'tcx>) -> UnordMap<Instance<'tcx>, PanicSpec> {
    let graph = genv.call_graph();

    let mut specs: UnordMap<Instance<'tcx>, PanicSpec> = UnordMap::default();
    let mut queue: VecDeque<Instance<'tcx>> = VecDeque::new();

    for (&instance, node) in &graph.nodes {
        let spec = initial_spec(genv, node, instance);
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
    specs
}

/// Computes the initial `PanicSpec` for a node before propagation.
///
/// `Analyzed` nodes with only resolved call sites and no explicit panics start as `WillNotPanic`
/// (optimistic). Every other node starts as `MightPanic` with the appropriate reason.
fn initial_spec<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
    node: &Node<'tcx>,
    instance: Instance<'tcx>,
) -> PanicSpec {
    match node {
        Node::ExternalCrate => genv.inferred_no_panic_external(instance),
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
