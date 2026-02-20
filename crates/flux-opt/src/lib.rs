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

/// The entry point for no-panic inference. Given a root function, explores its call graph and returns
/// an over-approximation of if it might panic, and why.
pub fn infer_no_panics(tcx: TyCtxt, root: DefId) -> FxHashMap<DefId, PanicSpec> {
    let mut fn_to_no_panic: FxHashMap<DefId, PanicSpec> = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut worklist: Vec<DefId> = vec![];

    if !tcx.def_kind(root).is_fn_like() {
        flux_common::bug!(
            "flux-opt::infer_no_panics: root DefId {} is not a function",
            tcx.def_path_str(root)
        );
    }

    if !tcx.is_mir_available(root) {
        let def_kind = tcx.def_kind(root);
        if matches!(def_kind, DefKind::AssocFn) {
            fn_to_no_panic.insert(
                root,
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::UnresolvedTraitMethod(root),
                )),
            );
        } else {
            fn_to_no_panic.insert(
                root,
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::NoMIRAvailable(root, tcx.def_kind(root)),
                )),
            );
        }
        return fn_to_no_panic;
    }

    match get_callees(&tcx, root) {
        Ok(callees) => {
            fn_to_no_panic.insert(root, PanicSpec::MightPanic(PanicReason::Unknown));
            call_graph.insert(root, callees);
        }
        Err(reason) => {
            fn_to_no_panic.insert(root, PanicSpec::MightPanic(PanicReason::CannotResolve(reason)));
            return fn_to_no_panic;
        }
    }
    worklist.push(root);

    // 2. Explore reachable callees (build closed call graph)
    while let Some(f) = worklist.pop() {
        let callees = call_graph.get(&f).unwrap().clone();

        for callee in callees {
            if is_panic_or_abort_fn(tcx, callee) {
                fn_to_no_panic.insert(f, PanicSpec::MightPanic(PanicReason::ContainsPanic));
                fn_to_no_panic.insert(callee, PanicSpec::MightPanic(PanicReason::ContainsPanic));
                continue;
            }

            if tcx.is_mir_available(callee) {
                if let hash_map::Entry::Vacant(e) = fn_to_no_panic.entry(callee) {
                    match get_callees(&tcx, callee) {
                        Ok(callees) => {
                            e.insert(PanicSpec::MightPanic(PanicReason::Unknown));
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        Err(reason) => {
                            e.insert(PanicSpec::MightPanic(PanicReason::CannotResolve(reason)));
                        }
                    }
                }
            } else {
                fn_to_no_panic.insert(
                    callee,
                    PanicSpec::MightPanic(PanicReason::CannotResolve(
                        CannotResolveReason::NoMIRAvailable(callee, tcx.def_kind(callee)),
                    )),
                );
            }
        }
    }

    // 3. Fixpoint: promote to WillNotPanic when all callees are WillNotPanic
    let mut changed = true;
    while changed {
        changed = false;

        let keys: Vec<DefId> = fn_to_no_panic.keys().copied().collect();

        for f in keys {
            // Skip already proven
            if matches!(fn_to_no_panic.get(&f), Some(PanicSpec::WillNotPanic)) {
                continue;
            }

            let callees = match call_graph.get(&f) {
                Some(callees) => callees,
                None => {
                    // This means that we hit a case where we couldn't resolve a callee.
                    continue;
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
                        // do we need this?
                        *entry = PanicSpec::MightPanic(PanicReason::Transitive);
                    }
                    PanicSpec::MightPanic(PanicReason::CannotResolve(_)) => {
                        // KEEP stronger reason — do not overwrite
                    }
                    PanicSpec::WillNotPanic
                    | PanicSpec::MightPanic(PanicReason::NotInCallGraph) => unreachable!(),
                }
            }
        }
    }

    let mut reason_to_count: FxHashMap<String, usize> = FxHashMap::default();
    for (_, reason) in &fn_to_no_panic {
        let key = match reason {
            PanicSpec::WillNotPanic => "WillNotPanic".to_string(),
            PanicSpec::MightPanic(r) => {
                match r {
                    PanicReason::Unknown => "Unknown".to_string(),
                    PanicReason::ContainsPanic => "ContainsPanic".to_string(),
                    PanicReason::Transitive => "Transitive".to_string(),
                    PanicReason::CannotResolve(reason) => {
                        match reason {
                            CannotResolveReason::UnresolvedTraitMethod(_) => {
                                "CannotResolve:UnresolvedTraitMethod".to_string()
                            }
                            CannotResolveReason::NotFnDef(_) => {
                                "CannotResolve:NotFnDef".to_string()
                            }
                            CannotResolveReason::NoMIRAvailable(_, _) => {
                                "CannotResolve:NoMIRAvailable".to_string()
                            }
                        }
                    }
                    PanicReason::NotInCallGraph => unreachable!(),
                }
            }
        };

        *reason_to_count.entry(key).or_default() += 1;
    }

    fn_to_no_panic
}
