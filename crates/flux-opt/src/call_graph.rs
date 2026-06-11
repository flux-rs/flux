use flux_middle::{
    call_graph::{CallGraph, CallSite, CallSiteKind, Node, NodeKey, resolved_callees},
    global_env::GlobalEnv,
};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE},
};
use rustc_middle::{
    mir::{Location, TerminatorKind, UnwindAction},
    ty::{EarlyBinder, Instance, InstanceKind, TyCtxt, TypingEnv},
};

pub fn build_call_graph<'tcx>(genv: GlobalEnv<'_, 'tcx>) -> CallGraph<'tcx> {
    let tcx = genv.tcx();

    let mut nodes: FxIndexMap<NodeKey<'_>, Node<'_>> = FxIndexMap::default();

    // Node-level worklist and visited set: the same DefId can appear both as a source item and as
    // distinct monomorphizations, each a separate [`NodeKey`].
    let mut worklist: Vec<NodeKey<'_>> = Vec::new();
    let mut explored: FxHashSet<NodeKey<'_>> = FxHashSet::default();

    for root_local in tcx.iter_local_def_id() {
        let def_id = root_local.to_def_id();
        if !tcx.def_kind(root_local).is_fn_like() || is_method_in_trait(tcx, def_id) {
            continue;
        }
        // Roots are the items as written in source.
        worklist.push(NodeKey::Item(def_id));
    }

    while let Some(key) = worklist.pop() {
        if !explored.insert(key) {
            continue;
        }
        let node = analyze_node(genv, key);
        worklist.extend(resolved_callees(node.call_sites()));
        nodes.insert(key, node);
    }

    CallGraph::new(nodes)
}

/// Classifies the node identified by `key` into a call-graph [`Node`], walking its body for call
/// sites when one is available.
fn analyze_node<'tcx>(genv: GlobalEnv<'_, 'tcx>, key: NodeKey<'tcx>) -> Node<'tcx> {
    let tcx = genv.tcx();
    let def_id = key.def_id();

    // External non-stdlib callees looked up from crate metadata.
    if !should_include_in_call_graph(genv, def_id.krate) {
        return Node::ExternalCrate;
    }

    let instance = key.instance(tcx);

    // Only `Item` instances have a walkable Rust body; shims / virtual stubs are leaves.
    //
    // For **local** functions we walk the unoptimized borrowck body (stashed by the `mir_borrowck`
    // override) rather than `tcx.instance_mir`, which would give us *optimized* MIR. This matters
    // because the checker recovers the resolved callee at a call site by `Location`, and those
    // locations must refer to the same (unoptimized) body the checker checks. See REPORT step 3.
    if let InstanceKind::Item(_) = instance.def {
        let call_sites = if let Some(local_def_id) = def_id.as_local() {
            // SAFETY: the call graph runs after rustc's analysis pass, so every local body has
            // been borrowchecked and stashed. `try_retrieve_mir_body` degrades to `None` (→ leaf)
            // for the rare local fn-like item rustc never borrowchecks.
            unsafe { flux_common::mir_storage::try_retrieve_mir_body(tcx, local_def_id) }
                .map(|facts| callees_in_body(tcx, instance, &facts.body))
        } else if tcx.is_mir_available(def_id) {
            Some(callees_in_body(tcx, instance, tcx.instance_mir(instance.def)))
        } else {
            None
        };
        if let Some(call_sites) = call_sites {
            return Node::Analyzed { call_sites };
        }
    }

    Node::Leaf(tcx.def_kind(def_id))
}

fn is_method_in_trait<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_kind = tcx.def_kind(def_id);
    if matches!(def_kind, DefKind::AssocFn) {
        matches!(tcx.associated_item(def_id).container, rustc_middle::ty::AssocContainer::Trait)
    } else {
        false
    }
}

fn should_include_in_call_graph(genv: GlobalEnv, krate: CrateNum) -> bool {
    krate == LOCAL_CRATE || is_outside_cstore(genv, krate) || is_stdlib_crate(genv, krate)
}

fn is_stdlib_crate(genv: GlobalEnv, krate: CrateNum) -> bool {
    matches!(genv.tcx().crate_name(krate).as_str(), "core" | "alloc" | "std")
}

fn is_outside_cstore(genv: GlobalEnv, krate: CrateNum) -> bool {
    // If the crate has no Flux metadata in the cratestore, flux never visited it,
    // so we should include that crate's functions in this call graph.
    !genv.cstore_has_crate(krate)
}

/// Walks `body`'s Call and Assert terminators, returning all call sites found.
fn callees_in_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> Vec<CallSite<'tcx>> {
    let typing_env = TypingEnv::non_body_analysis(tcx, caller.def_id());
    let mut call_sites = Vec::new();

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let terminator = bb_data.terminator();
        let location = Location { block: bb, statement_index: bb_data.statements.len() };

        let kind = match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let ty = func.ty(&body.local_decls, tcx);
                // The unoptimized borrowck body still carries region inference vars (`ReVar`),
                // which `instantiate_mir_and_normalize_erasing_regions` would panic on. Erase
                // regions up front — we only need the callee's type/const args to resolve it.
                let ty = tcx.erase_and_anonymize_regions(ty);
                // If we are inside a generic caller that we have monomorphized to a particular `Instance`,
                // we apply the caller's concrete args to get the concrete callee type. For generic callers
                // where `Instance` remains polymorphic (i.e., it has identity args) this is a no-op.
                let ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    typing_env,
                    EarlyBinder::bind(ty),
                );

                match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(callee_def_id, callee_args) => {
                        match Instance::try_resolve(tcx, typing_env, *callee_def_id, callee_args) {
                            Ok(Some(instance)) => {
                                CallSiteKind::Resolved { callee: NodeKey::from_instance(instance) }
                            }
                            _ => CallSiteKind::Unresolved { def_id: *callee_def_id },
                        }
                    }
                    _ => CallSiteKind::DynamicDispatch,
                }
            }
            TerminatorKind::Assert { unwind, .. }
                if !matches!(unwind, UnwindAction::Unreachable) =>
            {
                CallSiteKind::SynthesizedPanic
            }
            _ => continue,
        };
        call_sites.push(CallSite { location, kind });
    }

    call_sites
}
