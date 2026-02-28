#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_trait_selection;

use flux_rustc_bridge::lowering::resolve_call_query;
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::TerminatorKind,
    ty::{TyCtxt, TypingMode},
};
use rustc_trait_selection::traits::SelectionContext;

pub type CallGraph = FxHashMap<DefId, Vec<DefId>>;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum PanicSpec {
    WillNotPanic,
    MightPanic(PanicReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PanicReason {
    Unknown,
    ContainsPanic,
    Transitive,
    CannotResolve(CannotResolveReason),
    NotInCallGraph,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CannotResolveReason {
    NoMIRAvailable(DefId, DefKind),
    UnresolvedTraitMethod(DefId),
    NotFnDef(DefId),
}

#[derive(Debug, Clone)]
struct GraphBuildResult {
    call_graph: CallGraph,
    pub resolution_failures: FxHashMap<DefId, CannotResolveReason>,
}

fn panic_or_abort_fns(tcx: TyCtxt<'_>) -> Vec<DefId> {
    let lang_items = tcx.lang_items();
    [
        lang_items.panic_fn(),
        lang_items.panic_fmt(),
        lang_items.begin_panic_fn(),
        lang_items.panic_display(),
        lang_items.panic_cannot_unwind(),
    ]
    .into_iter()
    .filter_map(|item| item)
    .collect()
}

fn try_resolve<'tcx>(
    tcx: &TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<DefId, CannotResolveReason> {
    let param_env = tcx.param_env(def_id);
    let infcx = tcx
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());
    let mut selcx = SelectionContext::new(&infcx);

    let resolved = resolve_call_query(*tcx, &mut selcx, param_env, def_id, args);

    let Some((impl_id, _)) = resolved else {
        // Error case 1: we fail to resolve a trait method to an impl.
        return Err(CannotResolveReason::UnresolvedTraitMethod(def_id));
    };

    if !tcx.is_mir_available(impl_id) {
        return Err(CannotResolveReason::NoMIRAvailable(impl_id, tcx.def_kind(impl_id)));
    }

    Ok(impl_id)
}

// Grabs the callees of a function from its MIR.
// Returns Some(...) if all callees (1) are free functions, or (2) can be resolved to impl methods.
// If even one callee cannot be resolved, or is a closure, returns None.
pub(crate) fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Result<Vec<DefId>, CannotResolveReason> {
    let body = tcx.optimized_mir(def_id);

    let mut callees = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);
            // 1. Here, try to resolve the callee to either a method in an impl or a free function.
            // Otherwise, assume the caller can panic.
            // We can resolve the callee DefId by constructing a inferctxt from the tyctxt

            match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, args) => {
                    let Some(_trait_id) = tcx.trait_of_assoc(*def_id) else {
                        // If it's a free function, there's no need to resolve.
                        callees.push(*def_id);
                        continue;
                    };

                    let impl_id = try_resolve(tcx, *def_id, args)?;

                    if !tcx.is_mir_available(impl_id) {
                        return Err(CannotResolveReason::NoMIRAvailable(
                            impl_id,
                            tcx.def_kind(impl_id),
                        ));
                    }

                    callees.push(impl_id);
                }
                _ => {
                    // Error case 2: We're trying to reason about something that's not an FnDef.
                    return Err(CannotResolveReason::NotFnDef(def_id));
                }
            };
        }
    }
    Ok(callees)
}

fn build_closed_call_graph(
    tcx: TyCtxt,
    root: DefId,
    call_graph: &mut CallGraph,
    resolution_failures: &mut FxHashMap<DefId, CannotResolveReason>,
) {
    let mut worklist: Vec<DefId> = vec![root];
    // 2. Explore reachable callees (build closed call graph)
    while let Some(f) = worklist.pop() {
        let callees = call_graph.get(&f).unwrap().clone();

        for callee in callees {
            if !call_graph.contains_key(&callee) {
                if tcx.is_mir_available(callee) {
                    match get_callees(&tcx, callee) {
                        Ok(callees) => {
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        Err(reason) => {
                            resolution_failures.insert(callee, reason);
                            continue;
                        }
                    }
                } else {
                    resolution_failures.insert(
                        callee,
                        CannotResolveReason::NoMIRAvailable(callee, tcx.def_kind(callee)),
                    );
                    continue;
                }
            }

            if !call_graph.contains_key(&callee) {
                if tcx.is_mir_available(callee) {
                    match get_callees(&tcx, callee) {
                        Ok(callees) => {
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        Err(reason) => {
                            resolution_failures.insert(callee, reason);
                        }
                    }
                } else {
                    resolution_failures.insert(
                        callee,
                        CannotResolveReason::NoMIRAvailable(callee, tcx.def_kind(callee)),
                    );
                }
            }
        }
    }
}

fn explore_reachable_call_graph(tcx: TyCtxt, root: DefId) -> GraphBuildResult {
    let mut resolution_failures = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();

    if !tcx.def_kind(root).is_fn_like() {
        flux_common::bug!(
            "flux-opt::infer_no_panics: root DefId {} is not a function",
            tcx.def_path_str(root)
        );
    }

    if !tcx.is_mir_available(root) {
        let def_kind = tcx.def_kind(root);
        if matches!(def_kind, DefKind::AssocFn) {
            resolution_failures.insert(root, CannotResolveReason::UnresolvedTraitMethod(root));
        } else {
            resolution_failures.insert(root, CannotResolveReason::NoMIRAvailable(root, def_kind));
        }
        call_graph.insert(root, Vec::new());
        return GraphBuildResult { call_graph, resolution_failures };
    }

    match get_callees(&tcx, root) {
        Ok(callees) => {
            call_graph.insert(root, callees);
        }
        Err(reason) => {
            call_graph.insert(root, Vec::new());
            resolution_failures.insert(root, reason);
            return GraphBuildResult { call_graph, resolution_failures };
        }
    }

    build_closed_call_graph(tcx, root, &mut call_graph, &mut resolution_failures);

    GraphBuildResult { call_graph, resolution_failures }
}

fn run_fixpoint(
    call_graph: &CallGraph,
    fn_to_no_panic: &mut FxHashMap<DefId, PanicSpec>,
    panic_fns: &[DefId],
) {
    let mut changed = true;
    while changed {
        changed = false;

        let keys: Vec<DefId> = call_graph.keys().copied().collect();

        for f in keys {
            // Skip functions we've already seeded.
            let current_spec = fn_to_no_panic.get(&f).unwrap();

            match current_spec {
                PanicSpec::WillNotPanic
                | PanicSpec::MightPanic(
                    PanicReason::CannotResolve(_) | PanicReason::ContainsPanic,
                ) => {
                    continue;
                }
                _ => (),
            };

            if panic_fns.contains(&f) {
                fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::ContainsPanic));
                changed = true;
                continue;
            }

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

            if bad_callees.is_empty() {
                changed = true;
                fn_to_no_panic.insert(f, PanicSpec::WillNotPanic);
            } else if bad_callees.iter().any(|callee| panic_fns.contains(callee)) {
                changed = true;
                fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::ContainsPanic));
            } else if matches!(current_spec, PanicSpec::MightPanic(PanicReason::Unknown)) {
                let current_spec = fn_to_no_panic.get_mut(&f).unwrap();
                changed = true;
                *current_spec = PanicSpec::MightPanic(PanicReason::Transitive);
            }
        }
    }
}

/// The entry point for no-panic inference. Given a root function, explores its call graph and returns
/// an over-approximation of if it might panic, and why.
pub fn infer_no_panics(tcx: TyCtxt, root: DefId) -> FxHashMap<DefId, PanicSpec> {
    // 1. Build the call graph.
    let GraphBuildResult { call_graph, resolution_failures } =
        explore_reachable_call_graph(tcx, root);

    // 2. Seed the call graph with initial panic specs -- if the previous step found
    //    resolution failures, add those reasons here. Otherwise, seed with Unknown.
    let mut initial_specs: FxHashMap<DefId, PanicSpec> = FxHashMap::default();

    for def_id in call_graph.keys() {
        if let Some(resolution_error) = resolution_failures.get(def_id) {
            initial_specs.insert(
                *def_id,
                PanicSpec::MightPanic(PanicReason::CannotResolve(*resolution_error)),
            );
        } else {
            initial_specs.insert(*def_id, PanicSpec::MightPanic(PanicReason::Unknown));
        }
    }

    // 3. Run fixpoint to propagate panic specs through the call graph.
    let panic_fns = panic_or_abort_fns(tcx);
    run_fixpoint(&call_graph, &mut initial_specs, &panic_fns);

    initial_specs
}
