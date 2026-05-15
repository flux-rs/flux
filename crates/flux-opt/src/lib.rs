#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use flux_middle::{
    CannotResolveReason, PanicReason, PanicSpec, global_env::GlobalEnv, queries::Providers,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId, LOCAL_CRATE, LocalDefId},
    lang_items::LangItem,
};
use rustc_middle::{
    mir::{TerminatorKind, UnwindAction},
    ty::{EarlyBinder, GenericArgs, Instance, InstanceKind, TyCtxt, TypeVisitableExt, TypingEnv},
};

pub type CallGraph = FxHashMap<DefId, Vec<DefId>>;

pub fn provide(providers: &mut Providers) {
    providers.inferred_no_panic = inferred_no_panic;
}

pub fn inferred_no_panic(genv: GlobalEnv) -> FxHashMap<DefId, PanicSpec> {
    infer_no_panics(genv, |def_id| genv.inferred_no_panic(def_id))
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

#[derive(Debug, Clone)]
struct GraphBuildResult {
    call_graph: CallGraph,
    pub resolution_failures: FxHashMap<DefId, CannotResolveReason>,
    external_callees: FxHashSet<DefId>,
}

/// The entry point for no-panic inference. Given a root function, explores its call graph and returns
/// an over-approximation of if it might panic and why.
pub fn infer_no_panics(
    genv: GlobalEnv,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    let tcx = genv.tcx();

    // We need to use `iter_local_def_id` instead of `hir_body_owners`
    // so that we can visit trait items with no MIR.
    let roots: Vec<LocalDefId> = tcx
        .iter_local_def_id()
        .filter(|local_id| tcx.def_kind(local_id.to_def_id()).is_fn_like())
        .collect();

    // 1. Build the call graph.
    let GraphBuildResult { call_graph, resolution_failures, external_callees } =
        build_call_graph(genv, &roots);

    // 2. Seed the call graph with initial panic specs.
    //    - External non-stdlib callees: use the provided spec from their crate's metadata.
    //    - Resolution failures: seed with the failure reason.
    //    - Everything else: seed with Unknown for the fixpoint to resolve.
    let mut initial_specs: FxHashMap<DefId, PanicSpec> = FxHashMap::default();

    for def_id in call_graph.keys() {
        if external_callees.contains(def_id) {
            initial_specs.insert(*def_id, external_spec(*def_id));
        } else if let Some(resolution_error) = resolution_failures.get(def_id) {
            initial_specs.insert(
                *def_id,
                PanicSpec::MightPanic(PanicReason::CannotResolve(*resolution_error)),
            );
        } else {
            initial_specs.insert(*def_id, PanicSpec::MightPanic(PanicReason::Unknown));
        }
    }

    // 3. Run fixpoint to propagate panic specs through the call graph.
    run_fixpoint(&call_graph, &mut initial_specs);

    initial_specs
}

/// Builds the call graph starting from the local fn-like roots. If we encounter a call we
/// can't resolve, we add it to the resolution_failures map and keep going.
fn build_call_graph(genv: GlobalEnv, roots: &[LocalDefId]) -> GraphBuildResult {
    let tcx = genv.tcx();
    let mut resolution_failures = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut external_callees: FxHashSet<DefId> = FxHashSet::default();

    if roots
        .iter()
        .any(|root| !tcx.def_kind(root.to_def_id()).is_fn_like())
    {
        flux_common::bug!(
            "flux-opt::infer_no_panics: all roots must be fn-like, but found non-fn-like roots: {:?}",
            roots
                .iter()
                .filter(|root| !tcx.def_kind(root.to_def_id()).is_fn_like())
                .map(|root| tcx.def_path_str(root.to_def_id()))
                .collect::<Vec<_>>()
        );
    }

    explore(genv, roots, &mut call_graph, &mut resolution_failures, &mut external_callees);

    GraphBuildResult { call_graph, resolution_failures, external_callees }
}

/// Walks `body`'s Call terminators and resolves each callee to a concrete `Instance` using
/// the caller instance's type substitution. Returns the resolved callee instances and any
/// calls that could not be resolved.
///
/// `Assert` terminators with a non-unreachable unwind action can also panic — they have no
/// explicit callee in the MIR (`unwind: continue` propagates without any function call). We
/// synthesize a call to `core::panicking::panic` so the fixpoint sees the panic edge.
fn callees_in_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> (Vec<Instance<'tcx>>, Vec<(DefId, CannotResolveReason)>) {
    let typing_env = TypingEnv::non_body_analysis(tcx, caller.def_id());
    let mut callees = Vec::new();
    let mut failures = Vec::new();

    for bb in body.basic_blocks.iter() {
        match &bb.terminator().kind {
            TerminatorKind::Call { func, .. } => {
                let ty = func.ty(&body.local_decls, tcx);
                // Apply the caller's concrete type args to get the concrete callee type.
                // For non-generic callers this is a no-op; for generic stdlib bodies
                // this substitutes abstract type params with the concrete instantiation.
                let ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    typing_env,
                    EarlyBinder::bind(ty),
                );

                match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(callee_def_id, callee_args) => {
                        match Instance::try_resolve(tcx, typing_env, *callee_def_id, callee_args) {
                            Ok(Some(instance)) => callees.push(instance),
                            _ => {
                                failures.push((
                                    *callee_def_id,
                                    CannotResolveReason::UnresolvedTraitMethod(*callee_def_id),
                                ));
                            }
                        }
                    }
                    _ => {
                        // Function pointer or closure call — can't statically resolve.
                        failures.push((
                            caller.def_id(),
                            CannotResolveReason::NotFnDef(caller.def_id()),
                        ));
                    }
                }
            }
            TerminatorKind::Assert { unwind, .. }
                if !matches!(unwind, UnwindAction::Unreachable) =>
            {
                // An Assert with a reachable unwind path can panic without any explicit callee
                // (e.g. `unwind: continue` propagates with no cleanup call). Synthesize a call
                // to `core::panicking::panic` so the fixpoint sees the panic edge.
                if let Some(panic_def_id) = tcx.lang_items().get(LangItem::Panic) {
                    let panic_args = GenericArgs::identity_for_item(tcx, panic_def_id);
                    if let Ok(Some(instance)) =
                        Instance::try_resolve(tcx, typing_env, panic_def_id, panic_args)
                    {
                        callees.push(instance);
                    }
                }
            }
            _ => {}
        }
    }

    (callees, failures)
}

/// Callees of a local function. Uses `optimized_mir` (regions erased) rather than
/// the borrow-checked body to avoid region inference variables (`ReVar`) panicking
/// inside `instantiate_mir_and_normalize_erasing_regions`.
fn local_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_id: LocalDefId,
) -> (Vec<Instance<'tcx>>, Vec<(DefId, CannotResolveReason)>) {
    let def_id = local_id.to_def_id();
    let caller = Instance::new_raw(def_id, GenericArgs::identity_for_item(tcx, def_id));
    callees_in_body(tcx, caller, tcx.optimized_mir(def_id))
}

/// Callees of an external instance. Uses `instance_mir` so that
/// `instantiate_mir_and_normalize_erasing_regions` can substitute the concrete
/// args carried by `instance` into the generic stdlib body's call types.
fn extern_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> (Vec<Instance<'tcx>>, Vec<(DefId, CannotResolveReason)>) {
    callees_in_body(tcx, instance, tcx.instance_mir(instance.def))
}

fn explore<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
    roots: &[LocalDefId],
    call_graph: &mut CallGraph,
    resolution_failures: &mut FxHashMap<DefId, CannotResolveReason>,
    external_callees: &mut FxHashSet<DefId>,
) {
    let tcx = genv.tcx();
    // Instance-level worklist and visited set to handle the same DefId
    // being called with different concrete type args.
    let mut worklist: Vec<Instance<'tcx>> = Vec::new();
    let mut explored: FxHashSet<Instance<'tcx>> = FxHashSet::default();

    // 1. Seed the worklist with the root functions, and add their callees to the call graph.
    for &root_local in roots {
        let root = root_local.to_def_id();

        if !tcx.is_mir_available(root) {
            let def_kind = tcx.def_kind(root);
            if matches!(def_kind, DefKind::AssocFn) {
                resolution_failures.insert(root, CannotResolveReason::UnresolvedTraitMethod(root));
            } else {
                resolution_failures
                    .insert(root, CannotResolveReason::NoMIRAvailable(root, def_kind));
            }
            call_graph.insert(root, Vec::new());
            continue;
        }

        let (callee_instances, failures) = local_callees(tcx, root_local);
        for (failed_id, reason) in failures {
            call_graph.entry(failed_id).or_default();
            resolution_failures.entry(failed_id).or_insert(reason);
        }
        let callee_def_ids: Vec<DefId> = callee_instances.iter().map(|i| i.def_id()).collect();
        call_graph.insert(root, callee_def_ids);
        worklist.extend(callee_instances);
    }

    while let Some(instance) = worklist.pop() {
        if explored.contains(&instance) {
            continue;
        }
        explored.insert(instance);

        let def_id = instance.def_id();

        // External non-stdlib callees: treat as a leaf and record for spec lookup.
        if !should_include_in_call_graph(genv, def_id.krate) {
            call_graph.entry(def_id).or_default();
            external_callees.insert(def_id);
            continue;
        }

        // Only Item instances have MIR we can walk; shims, intrinsics, and
        // virtual-dispatch stubs are treated as opaque leaves.
        // If the instance still carries abstract type/const params (it was resolved in a
        // generic context), normalization inside its body would panic — treat as opaque leaf.
        let has_abstract_args = instance.args.has_param();
        if matches!(instance.def, InstanceKind::Item(_))
            && tcx.is_mir_available(def_id)
            && !has_abstract_args
        {
            let (callee_instances, failures) = extern_callees(tcx, instance);
            for (failed_id, reason) in failures {
                call_graph.entry(failed_id).or_default();
                resolution_failures.entry(failed_id).or_insert(reason);
            }
            let callee_def_ids: Vec<DefId> = callee_instances.iter().map(|i| i.def_id()).collect();
            // or_insert so the first concrete instantiation of a DefId wins;
            // subsequent instantiations still push their callees onto the worklist.
            call_graph.entry(def_id).or_insert(callee_def_ids);
            worklist.extend(callee_instances);
        } else if matches!(instance.def, InstanceKind::Item(_))
            && !tcx.is_mir_available(def_id)
            && !has_abstract_args
        {
            // Item with no MIR and concrete args (e.g. extern "C" or platform-specific
            // functions). We can't analyze it, so conservatively treat as might panic.
            call_graph.entry(def_id).or_default();
            resolution_failures
                .entry(def_id)
                .or_insert(CannotResolveReason::NoMIRAvailable(def_id, tcx.def_kind(def_id)));
        } else {
            // Non-Item instance (shim, intrinsic, virtual dispatch stub) or abstract args:
            // treat as opaque WillNotPanic leaf.
            call_graph.entry(def_id).or_default();
        }
    }
}

/// Runs a fixpoint algorithm over the call graph to propagate panic specs.
/// If all callees are known to not panic, then this function is known to not panic.
/// If a function has a callee that might panic, then it transitively might panic.
fn run_fixpoint(call_graph: &CallGraph, fn_to_no_panic: &mut FxHashMap<DefId, PanicSpec>) {
    let mut changed = true;
    while changed {
        changed = false;

        let keys: Vec<DefId> = call_graph.keys().copied().collect();

        for f in keys {
            // Skip functions we've already seeded.
            let current_spec = fn_to_no_panic.get(&f).unwrap();

            match current_spec {
                PanicSpec::WillNotPanic | PanicSpec::MightPanic(PanicReason::CannotResolve(_)) => {
                    continue;
                }
                _ => (),
            };

            let callees = match call_graph.get(&f) {
                Some(callees) => callees,
                None => {
                    unreachable!("run_fixpoint: call graph should contain all reachable functions");
                }
            };

            let mut bad_callees = Vec::new();

            for callee in callees {
                match fn_to_no_panic.get(callee) {
                    Some(PanicSpec::WillNotPanic) => {}
                    _ => bad_callees.push(*callee),
                }
            }

            // Case 1: All callees are known to not panic, so this function is also known to not panic.
            if bad_callees.is_empty() {
                changed = true;
                fn_to_no_panic.insert(f, PanicSpec::WillNotPanic);
            // Case 2: This function has a callee that transitively might panic, so this function transitively might panic.
            } else if matches!(current_spec, PanicSpec::MightPanic(PanicReason::Unknown)) {
                let current_spec = fn_to_no_panic.get_mut(&f).unwrap();
                changed = true;
                *current_spec = PanicSpec::MightPanic(PanicReason::Transitive);
            }
        }
    }
}
