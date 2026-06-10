use flux_middle::{
    call_graph::{CallGraph, CallSite, CallSiteKind, NodeInfo, NodeKind, resolved_callees},
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
    ty::{EarlyBinder, GenericArgs, Instance, InstanceKind, TyCtxt, TypeVisitableExt, TypingEnv},
};

pub fn build_call_graph<'tcx>(genv: GlobalEnv<'_, 'tcx>) -> CallGraph<'tcx> {
    let tcx = genv.tcx();

    let mut nodes: FxIndexMap<Instance<'_>, NodeInfo<'_>> = FxIndexMap::default();

    // Instance-level worklist and visited set to handle the same DefId being
    // called with different concrete type args.
    let mut worklist: Vec<Instance<'_>> = Vec::new();
    let mut explored: FxHashSet<Instance<'_>> = FxHashSet::default();

    for root_local in tcx.iter_local_def_id() {
        let def_id = root_local.to_def_id();
        if !tcx.def_kind(root_local).is_fn_like() || is_method_in_trait(tcx, def_id) {
            continue;
        }
        worklist.push(Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id)));
    }

    while let Some(instance) = worklist.pop() {
        if !explored.insert(instance) {
            continue;
        }

        let def_id = instance.def_id();

        // External non-stdlib callees: treat as a leaf and record for spec lookup.
        if !should_include_in_call_graph(genv, def_id.krate) {
            nodes.insert(instance, NodeInfo { kind: NodeKind::ExternalCrate, call_sites: vec![] });
            continue;
        }

        if let InstanceKind::Item(_) = instance.def
            && tcx.is_mir_available(def_id)
        {
            let call_sites = item_callees(tcx, instance);
            worklist.extend(resolved_callees(&call_sites));
            let is_mono = !is_identity_instance(tcx, instance);
            nodes.insert(instance, NodeInfo { kind: NodeKind::Analyzed { is_mono }, call_sites });
        } else {
            nodes.insert(
                instance,
                NodeInfo { kind: NodeKind::Leaf(tcx.def_kind(def_id)), call_sites: vec![] },
            );
        }
    }

    CallGraph::new(nodes)
}

fn is_method_in_trait<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_kind = tcx.def_kind(def_id);
    if matches!(def_kind, DefKind::AssocFn) {
        matches!(tcx.associated_item(def_id).container, rustc_middle::ty::AssocContainer::Trait)
    } else {
        false
    }
}

fn is_identity_instance<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> bool {
    let identity = GenericArgs::identity_for_item(tcx, instance.def_id());
    instance.args == identity
}

/// If `instance` is an `InstanceKind::Item` whose args still contain abstract type/const
/// parameters (i.e., we are inside a generic caller), normalize it to its identity instance so
/// all call sites for the same generic function fold into one graph node.
fn normalize_abstract_args<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Instance<'tcx> {
    if matches!(instance.def, InstanceKind::Item(_)) && instance.args.has_param() {
        let def_id = instance.def_id();
        Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id))
    } else {
        instance
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
                // Apply the caller's concrete type args to get the concrete callee type.
                let ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    typing_env,
                    EarlyBinder::bind(ty),
                );

                match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(callee_def_id, callee_args) => {
                        match Instance::try_resolve(tcx, typing_env, *callee_def_id, callee_args) {
                            Ok(Some(instance)) => {
                                CallSiteKind::Resolved {
                                    callee: normalize_abstract_args(tcx, instance),
                                }
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

/// Call sites of a worklist instance. After normalization all non-mono instances on the worklist
/// are identity instances, so `instance_mir` returns the unspecialized body.
fn item_callees<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Vec<CallSite<'tcx>> {
    callees_in_body(tcx, instance, tcx.instance_mir(instance.def))
}
