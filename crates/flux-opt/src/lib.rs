#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_trait_selection;

use std::collections::hash_map;

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

struct CallGraphResult {
    call_graph: CallGraph,
    resolution_failures: FxHashMap<DefId, CannotResolveReason>,
}

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
    NoMIRAvailable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CannotResolveReason {
    NoMIRAvailable(DefId, DefKind),
    UnresolvedTraitMethod(DefId),
    NotFnDef(DefId),
}

fn is_panic_or_abort_fn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let lang_items = tcx.lang_items();
    [
        lang_items.panic_fn(),
        lang_items.panic_fmt(),
        lang_items.begin_panic_fn(),
        lang_items.panic_display(),
        lang_items.panic_cannot_unwind(),
    ]
    .into_iter()
    .flatten()
    .any(|lid| lid == def_id)
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
// Returns Ok(callee_def_ids) if all callees (1) are free functions, or (2) can be resolved to impl methods.
// If even one callee cannot be resolved, or is a closure, returns Err(reason).
// Panics
// The caller is responsible for ensuring that the given def_id is a function and has MIR available.
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

fn explore_reachable_call_graph(tcx: TyCtxt, root: DefId) -> CallGraphResult {
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut resolution_failures: FxHashMap<DefId, CannotResolveReason> = FxHashMap::default();
    let mut worklist: Vec<DefId> = vec![root];

    if !tcx.def_kind(root).is_fn_like() {
        flux_common::bug!(
            "flux-opt::infer_no_panics: root DefId {} is not a function",
            tcx.def_path_str(root)
        );
    }

    // 2. Explore reachable callees (build closed call graph)
    while let Some(f) = worklist.pop() {
        if call_graph.contains_key(&f) {
            continue;
        }

        if !tcx.is_mir_available(f) {
            call_graph.insert(f, vec![]);
            continue;
        }

        match get_callees(&tcx, f) {
            Ok(callees) => {
                call_graph.insert(f, callees.clone());
                for callee in callees {
                    worklist.push(callee);
                }
            }
            Err(e) => {
                call_graph.insert(f, vec![]);
                resolution_failures.insert(f, e);
            }
        };
    }
    CallGraphResult { call_graph, resolution_failures }
}

fn run_fixpoint(
    call_graph_result: &CallGraphResult,
    fn_to_no_panic: &mut FxHashMap<DefId, PanicSpec>,
) {
    let CallGraphResult { call_graph, resolution_failures } = call_graph_result;
    let mut changed = true;
    while changed {
        changed = false;

        let keys: Vec<DefId> = fn_to_no_panic.keys().copied().collect();

        for f in keys {
            // Skip already proven
            if !matches!(fn_to_no_panic.get(&f), Some(PanicSpec::MightPanic(PanicReason::Unknown)))
            {
                continue;
            }

            let callees = call_graph
                .get(&f)
                .expect("call graph should contain all reachable functions");

            if let Some(reason) = resolution_failures.get(&f) {
                fn_to_no_panic
                    .insert(f, PanicSpec::MightPanic(PanicReason::CannotResolve(*reason)));
                continue;
            }

            let mut bad_callees = Vec::new();

            for callee in callees {
                match fn_to_no_panic.get(callee) {
                    Some(PanicSpec::WillNotPanic) => {}
                    _ => bad_callees.push(*callee),
                }
            }

            if bad_callees.is_empty() {
                fn_to_no_panic.insert(f, PanicSpec::WillNotPanic);
                changed = true;
            } else {
                let entry = fn_to_no_panic.get_mut(&f).unwrap();

                // TODO: make this a helper method
                match entry {
                    PanicSpec::MightPanic(PanicReason::ContainsPanic) => {
                        // This is first: we saw a direct panic in this function's body.
                    }
                    PanicSpec::MightPanic(PanicReason::Unknown) => {
                        *entry = PanicSpec::MightPanic(PanicReason::Transitive);
                    }
                    PanicSpec::MightPanic(PanicReason::Transitive) => {
                        // KEEP same reason — do not overwrite
                    }
                    PanicSpec::MightPanic(PanicReason::CannotResolve(_)) => {
                        // KEEP stronger reason — do not overwrite
                    }
                    PanicSpec::MightPanic(PanicReason::NoMIRAvailable) => {
                        // KEEP stronger reason — do not overwrite
                    }
                    PanicSpec::WillNotPanic
                    | PanicSpec::MightPanic(PanicReason::NotInCallGraph) => unreachable!(),
                }
            }
        }
    }
}

/// The entry point for no-panic inference. Given a root function, explores its call graph and returns
/// an over-approximation of if it might panic, and why.
pub fn infer_no_panics(tcx: TyCtxt, root: DefId) -> FxHashMap<DefId, PanicSpec> {
    let mut fn_to_no_panic: FxHashMap<DefId, PanicSpec> = Default::default();
    let CallGraphResult { call_graph, resolution_failures } =
        explore_reachable_call_graph(tcx, root);

    // 1. Initialize all functions as "might panic" or "contains panic".
    for (&f, callees) in call_graph.iter() {
        // Default assumption: "could panic"
        fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::Unknown));

        if is_panic_or_abort_fn(tcx, f) {
            fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::ContainsPanic));
        } else if !tcx.is_mir_available(f) {
            let def_kind = tcx.def_kind(f);
            if matches!(def_kind, DefKind::AssocFn) {
                fn_to_no_panic.insert(
                    f,
                    PanicSpec::MightPanic(PanicReason::CannotResolve(
                        CannotResolveReason::UnresolvedTraitMethod(f),
                    )),
                );
            } else {
                fn_to_no_panic.insert(
                    f,
                    PanicSpec::MightPanic(PanicReason::CannotResolve(
                        CannotResolveReason::NoMIRAvailable(f, def_kind),
                    )),
                );
            }
        } else if let Err(reason) = get_callees(&tcx, f) {
            fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::CannotResolve(reason)));
            continue;
        }

        if callees.iter().any(|&c| is_panic_or_abort_fn(tcx, c)) {
            fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::ContainsPanic));
        }
    }

    let cg = call_graph.clone();

    run_fixpoint(&CallGraphResult { call_graph: cg, resolution_failures }, &mut fn_to_no_panic);
    assert_eq!(call_graph.len(), fn_to_no_panic.len());

    fn_to_no_panic
}
