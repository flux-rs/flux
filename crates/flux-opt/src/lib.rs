#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_trait_selection;

use flux_middle::{CannotResolveReason, PanicReason, PanicSpec};
use flux_rustc_bridge::lowering::resolve_call_query;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::DefKind,
    def_id::{CrateNum, DefId},
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::TerminatorKind,
    ty::{TyCtxt, TypingMode},
};
use rustc_trait_selection::traits::SelectionContext;

pub type CallGraph = FxHashMap<DefId, Vec<DefId>>;

fn is_stdlib_crate(tcx: TyCtxt, krate: CrateNum) -> bool {
    matches!(tcx.crate_name(krate).as_str(), "core" | "alloc" | "std")
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
    tcx: TyCtxt,
    crate_num: CrateNum,
    external_spec: impl Fn(DefId) -> PanicSpec,
) -> FxHashMap<DefId, PanicSpec> {
    let roots = tcx
        .hir_body_owners()
        .filter_map(|def_id| {
            let def_id = def_id.to_def_id();
            if tcx.def_kind(def_id).is_fn_like() { Some(def_id) } else { None }
        })
        .collect::<Vec<_>>();

    // 1. Build the call graph.
    let GraphBuildResult { call_graph, resolution_failures, external_callees } =
        build_call_graph(tcx, crate_num, &roots.as_slice());

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

/// Builds the call graph starting from the root function. If we encounter a call we can't resolve, we add it to the resolution_failures map and keep going.
fn build_call_graph(tcx: TyCtxt, crate_num: CrateNum, roots: &[DefId]) -> GraphBuildResult {
    let mut resolution_failures = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut external_callees: FxHashSet<DefId> = FxHashSet::default();

    if roots.iter().any(|root| !tcx.def_kind(*root).is_fn_like()) {
        flux_common::bug!(
            "flux-opt::infer_no_panics: all root DefIds must be functions, but found non-function roots: {:?}",
            roots
                .iter()
                .filter(|root| !tcx.def_kind(**root).is_fn_like())
                .map(|root| tcx.def_path_str(*root))
                .collect::<Vec<_>>()
        );
    }

    explore(
        tcx,
        crate_num,
        roots,
        &mut call_graph,
        &mut resolution_failures,
        &mut external_callees,
    );

    GraphBuildResult { call_graph, resolution_failures, external_callees }
}

/// Tries to resolve a trait method call to an impl method. If successful, returns the DefId of the impl method.
fn try_resolve<'tcx>(
    tcx: &TyCtxt<'tcx>,
    caller_id: DefId,
    callee_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<DefId, CannotResolveReason> {
    let param_env = tcx.param_env(caller_id);
    let infcx = tcx
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());
    let mut selcx = SelectionContext::new(&infcx);

    let resolved = resolve_call_query(*tcx, &mut selcx, param_env, callee_id, args);

    let Some((impl_id, _)) = resolved else {
        // Error case 1: we fail to resolve a trait method to an impl.
        return Err(CannotResolveReason::UnresolvedTraitMethod(callee_id));
    };

    if !tcx.is_mir_available(impl_id) {
        return Err(CannotResolveReason::NoMIRAvailable(impl_id, tcx.def_kind(impl_id)));
    }

    Ok(impl_id)
}

/// Returns the callees of a function as (resolved, failures), where failures are
/// (callee_def_id, reason) pairs. Continues past individual resolution failures
/// rather than short-circuiting, so all reachable callees end up in the call graph.
fn get_callees(tcx: &TyCtxt, def_id: DefId) -> (Vec<DefId>, Vec<(DefId, CannotResolveReason)>) {
    // let body = if def_id.is_local() {
    //     // genv.mir(def_id.expect_local())
    //     tcx.mir_built(def_id.expect_local())
    // } else {
    //     tcx.optimized_mir(def_id)
    // }
    let body = tcx.optimized_mir(def_id);

    let mut resolved = Vec::new();
    let mut failures = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);

            match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(callee_id, args) => {
                    let Some(_trait_id) = tcx.trait_of_assoc(*callee_id) else {
                        // Free function — no resolution needed.
                        resolved.push(*callee_id);
                        continue;
                    };

                    match try_resolve(tcx, def_id, *callee_id, args) {
                        Err(reason) => {
                            failures.push((*callee_id, reason));
                        }
                        Ok(impl_id) => {
                            if !tcx.is_mir_available(impl_id) {
                                failures.push((
                                    impl_id,
                                    CannotResolveReason::NoMIRAvailable(
                                        impl_id,
                                        tcx.def_kind(impl_id),
                                    ),
                                ));
                            } else {
                                resolved.push(impl_id);
                            }
                        }
                    }
                }
                _ => {
                    // Not an FnDef (e.g. function pointer / closure) — use caller as sentinel.
                    failures.push((def_id, CannotResolveReason::NotFnDef(def_id)));
                }
            };
        }
    }
    (resolved, failures)
}

/// Explores the call graph starting from the root function, populating the call graph and resolution failures.
fn explore(
    tcx: TyCtxt,
    crate_num: CrateNum,
    roots: &[DefId],
    call_graph: &mut CallGraph,
    resolution_failures: &mut FxHashMap<DefId, CannotResolveReason>,
    external_callees: &mut FxHashSet<DefId>,
) {
    let mut worklist: Vec<DefId> = roots.to_vec();

    // Helper: register individual callee failures as leaves in the call graph.
    let register_failures =
        |call_graph: &mut CallGraph,
         resolution_failures: &mut FxHashMap<DefId, CannotResolveReason>,
         failures: Vec<(DefId, CannotResolveReason)>| {
            for (failed_id, reason) in failures {
                call_graph.entry(failed_id).or_default();
                resolution_failures.entry(failed_id).or_insert(reason);
            }
        };

    // 1. Seed the worklist with the root functions, and add their callees to the call graph.
    for root in roots {
        let root = *root;
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

        let (resolved, failures) = get_callees(&tcx, root);
        // println!("callees of {}:", tcx.def_path_str(root));
        // println!("resolved:");
        // for callee in &resolved {
        //     println!("  {}", tcx.def_path_str(*callee));
        // }

        // println!("failures:");
        // for (failed_id, reason) in &failures {
        //     println!("  {}: {:?}", tcx.def_path_str(*failed_id), reason);
        // }
        // println!("MIR of root:");
        // println!("{:#?}", tcx.optimized_mir(root));
        register_failures(call_graph, resolution_failures, failures);
        call_graph.insert(root, resolved);
    }

    // 2. Explore reachable callees (build closed call graph)
    while let Some(f) = worklist.pop() {
        let callees = call_graph.get(&f).unwrap().clone();

        for callee in callees {
            if call_graph.contains_key(&callee) {
                continue;
            }

            // External non-stdlib callees: treat as a leaf and record for spec lookup.
            if callee.krate != crate_num && !is_stdlib_crate(tcx, callee.krate) {
                call_graph.entry(callee).or_insert_with(Vec::new);
                external_callees.insert(callee);
                continue;
            }

            if tcx.is_mir_available(callee) {
                let (resolved, failures) = get_callees(&tcx, callee);
                register_failures(call_graph, resolution_failures, failures);
                call_graph.insert(callee, resolved);
                worklist.push(callee);
            } else {
                call_graph.entry(callee).or_default();
                resolution_failures.insert(
                    callee,
                    CannotResolveReason::NoMIRAvailable(callee, tcx.def_kind(callee)),
                );
            }
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
