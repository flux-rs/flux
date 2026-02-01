#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_trait_selection;

use std::collections::HashSet;

use flux_common::bug;
use flux_rustc_bridge::lowering::{resolve_call_query, resolve_trait_ref_impl_id};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::{Body, Operand, StatementKind, TerminatorKind},
    ty::{self as rustc_ty, TyCtxt, TypingMode},
};
use rustc_trait_selection::traits::SelectionContext;

pub type CallGraph = FxHashMap<DefId, Vec<DefId>>;

mod visualize;

// NOTE by Andrew @ninehusky:
// I kind of want to push this through to the top-level flux attributes.
// The true/falseness of "no panic" gives me this double negation
// that I always mess up.
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
    NoMIRAvailable(DefId),
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

                    let param_env = tcx.param_env(def_id);
                    let infcx = tcx
                        .infer_ctxt()
                        .with_next_trait_solver(true)
                        .build(TypingMode::non_body_analysis());
                    let mut selcx = SelectionContext::new(&infcx);

                    let resolved = resolve_call_query(*tcx, &mut selcx, param_env, *def_id, args);

                    let Some((impl_id, _)) = resolved else {
                        // Error case 1: we fail to resolve a trait method to an impl.
                        return Err(CannotResolveReason::UnresolvedTraitMethod(*def_id));
                    };

                    if !tcx.is_mir_available(impl_id) {
                        return Err(CannotResolveReason::NoMIRAvailable(impl_id));
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

fn strength(spec: &PanicSpec) -> u8 {
    // This is my attempt to make a lattice for PanicSpec strengths.
    match spec {
        PanicSpec::WillNotPanic => 0,
        PanicSpec::MightPanic(r) => {
            match r {
                // Panic analysis couldn't figure it out.
                // This shouldn't appear in the final results;
                // it should always be refined to something stronger.
                PanicReason::Unknown => 1,

                // We still can't figure it out, but we have a reason
                // why we can't figure it out.
                PanicReason::CannotResolve(_) => 2,

                // We know this function is bad because of specific callees.
                PanicReason::Transitive => 3,

                // We saw an actual panic.
                PanicReason::ContainsPanic => 4,

                PanicReason::NotInCallGraph => unreachable!(),
            }
        }
    }
}

pub fn infer_no_panics(tcx: TyCtxt, root: DefId) -> FxHashMap<DefId, PanicSpec> {
    let mut fn_to_no_panic: FxHashMap<DefId, PanicSpec> = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut worklist: Vec<DefId> = vec![];

    // 1. Seed with all local MIR-owning functions
    for def_id in &[root] {
        let def_id = *def_id;
        println!("name: {}", tcx.def_path_str(def_id));

        if !tcx.def_kind(def_id).is_fn_like() {
            continue;
        }

        if !tcx.is_mir_available(def_id) {
            // Should not happen for locals
            eprintln!("Missing MIR for local function: {}", tcx.def_path_str(def_id));
            fn_to_no_panic.insert(
                def_id,
                PanicSpec::MightPanic(PanicReason::CannotResolve(
                    CannotResolveReason::NoMIRAvailable(def_id),
                )),
            );
            return fn_to_no_panic;
        }

        match get_callees(&tcx, def_id) {
            Ok(callees) => {
                fn_to_no_panic.insert(def_id, PanicSpec::MightPanic(PanicReason::Unknown));
                call_graph.insert(def_id, callees);
            }
            Err(reason) => {
                fn_to_no_panic
                    .insert(def_id, PanicSpec::MightPanic(PanicReason::CannotResolve(reason)));
                continue;
            }
        }
        worklist.push(def_id);
    }

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
                if !fn_to_no_panic.contains_key(&callee) {
                    match get_callees(&tcx, callee) {
                        Ok(callees) => {
                            fn_to_no_panic
                                .insert(callee, PanicSpec::MightPanic(PanicReason::Unknown));
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        Err(reason) => {
                            fn_to_no_panic.insert(
                                callee,
                                PanicSpec::MightPanic(PanicReason::CannotResolve(reason)),
                            );
                        }
                    }
                }
            } else {
                // TODO: make this `ContainsPanic` thing more descriptive
                fn_to_no_panic.insert(callee, PanicSpec::MightPanic(PanicReason::ContainsPanic));
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
    for (_, reason) in fn_to_no_panic.iter() {
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
                            CannotResolveReason::NoMIRAvailable(_) => {
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

    // for no_mir_fn in fn_to_no_panic.iter().filter_map(|(&k, v)| {
    //     if let PanicSpec::MightPanic(PanicReason::CannotResolve(
    //         CannotResolveReason::NoMIRAvailable(_),
    //     )) = v
    //     {
    //         Some(k)
    //     } else {
    //         None
    //     }
    // }) {
    //     let name = tcx.def_path_str(no_mir_fn);
    //     println!("  No MIR function: {}", name);
    // }

    // println!("=== no-panic inference results ===");
    // for (reason, count) in reason_to_count {
    //     println!("{:4}  {}", count, reason);
    // }

    // visualize::visualize(&tcx, call_graph, "button.rs", &fn_to_no_panic);

    fn_to_no_panic
}
