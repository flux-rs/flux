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
#[derive(Debug, Clone)]
pub enum PanicSpec {
    WillNotPanic,
    MightPanic(PanicReason),
}

#[derive(Debug, Clone)]
pub enum PanicReason {
    Unknown,
    ContainsPanic,
    Transitive(Vec<DefId>),
    CallsTraitMethod(String),
    CallsMethodForNoMIR(String),
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
pub(crate) fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Option<Vec<DefId>> {
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
                    // 1. resolve.
                    let Some(trait_id) = tcx.trait_of_assoc(*def_id) else {
                        // Case 1: it's a free function.
                        callees.push(*def_id);
                        continue;
                    };

                    // Case 2: it's a trait method.
                    let trait_ref = rustc_ty::TraitRef::from_assoc(*tcx, trait_id, *args);
                    let param_env = tcx.param_env(def_id);
                    let infcx = tcx
                        .infer_ctxt()
                        .with_next_trait_solver(true)
                        .build(TypingMode::non_body_analysis());
                    let mut selcx = SelectionContext::new(&infcx);

                    let resolved = resolve_call_query(*tcx, &mut selcx, param_env, *def_id, args);

                    let Some((impl_id, _)) = resolved else {
                        return None;
                    };
                    callees.push(impl_id);
                }
                _ => {
                    return None;
                }
            };
        }
    }
    Some(callees)
}

pub fn infer_no_panics(tcx: TyCtxt) -> FxHashMap<DefId, bool> {
    let mut fn_to_no_panic: FxHashMap<DefId, PanicSpec> = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();
    let mut worklist: Vec<DefId> = vec![];

    // 1. Seed with all local MIR-owning functions
    for local in tcx.hir_body_owners() {
        let def_id = local.to_def_id();

        if !tcx.def_kind(def_id).is_fn_like() {
            continue;
        }

        if !tcx.is_mir_available(def_id) {
            // Should not happen for locals
            bug!("missing MIR for local function");
        }

        match get_callees(&tcx, def_id) {
            Some(callees) => {
                fn_to_no_panic.insert(def_id, PanicSpec::MightPanic(PanicReason::Unknown));
                call_graph.insert(def_id, callees);
            }
            None => {
                // Cannot resolve callees: assume might panic
                // for now, i'm labelling this as "has panic", but later i'll update this
                // to have a more accurate signal.
                fn_to_no_panic.insert(def_id, PanicSpec::MightPanic(PanicReason::ContainsPanic));
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
                        Some(callees) => {
                            fn_to_no_panic
                                .insert(callee, PanicSpec::MightPanic(PanicReason::Unknown));
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        None => {
                            // Callee has unresolved calls ⇒ conservatively might panic
                            fn_to_no_panic
                                .insert(callee, PanicSpec::MightPanic(PanicReason::ContainsPanic));
                            // Intentionally do NOT add to call_graph or worklist
                        }
                    }
                }
            } else {
                // no MIR (extern, intrinsic, etc.)
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

                match entry {
                    PanicSpec::MightPanic(PanicReason::ContainsPanic) => {
                        // KEEP strongest reason — do not overwrite
                    }
                    PanicSpec::MightPanic(PanicReason::Unknown) => {
                        *entry = PanicSpec::MightPanic(PanicReason::Transitive(bad_callees));
                    }
                    PanicSpec::MightPanic(PanicReason::Transitive(_)) => {
                        // OK to refine transitive → more precise transitive
                        *entry = PanicSpec::MightPanic(PanicReason::Transitive(bad_callees));
                    }
                    PanicSpec::MightPanic(
                        PanicReason::CallsTraitMethod(_) | PanicReason::CallsMethodForNoMIR(_),
                    ) => {
                        // KEEP stronger reason — do not overwrite
                    }
                    PanicSpec::WillNotPanic => unreachable!(),
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
                    PanicReason::Transitive(_) => "Transitive".to_string(),
                    PanicReason::CallsTraitMethod(_) => "CallsTraitMethod".to_string(),
                    PanicReason::CallsMethodForNoMIR(_) => "CallsMethodForNoMIR".to_string(),
                }
            }
        };

        *reason_to_count.entry(key).or_default() += 1;
    }

    for no_mir_fn in fn_to_no_panic.iter().filter_map(|(&k, v)| {
        if let PanicSpec::MightPanic(PanicReason::CallsMethodForNoMIR(_)) = v {
            Some(k)
        } else {
            None
        }
    }) {
        let name = tcx.def_path_str(no_mir_fn);
        println!("  No MIR function: {}", name);
    }

    println!("=== no-panic inference results ===");
    for (reason, count) in reason_to_count {
        println!("{:4}  {}", count, reason);
    }

    visualize::visualize(&tcx, call_graph, "button.rs", &fn_to_no_panic);

    fn_to_no_panic
        .iter()
        .map(|(&k, v)| (k, matches!(v, PanicSpec::WillNotPanic)))
        .collect::<FxHashMap<DefId, bool>>()
}
