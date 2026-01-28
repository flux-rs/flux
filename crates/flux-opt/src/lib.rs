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

// TODO: make this return a Option<DefId> in the cases where we can't see that the ty.kind() is an FnDef.
pub(crate) fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Vec<DefId> {
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
                        // unable to resolve impl — assume the worst.
                        println!(
                            "I can't resolve the impl for trait method: {}",
                            tcx.def_path_str(*def_id)
                        );
                        continue;
                    };
                    callees.push(impl_id);
                }
                _ => (),
            };
        }
    }
    callees
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

        fn_to_no_panic.insert(def_id, PanicSpec::MightPanic(PanicReason::Unknown));
        call_graph.insert(def_id, get_callees(&tcx, def_id));
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
                    fn_to_no_panic.insert(callee, PanicSpec::MightPanic(PanicReason::Unknown));
                    call_graph.insert(callee, get_callees(&tcx, callee));
                    worklist.push(callee);
                }
            } else {
                let fn_name = tcx.def_path_str(callee);

                // Missing MIR: record *why* f cannot be proven no-panic
                println!("I can't find the MIR for function: {}", fn_name);

                let reason = match tcx.def_kind(callee) {
                    rustc_hir::def::DefKind::AssocFn => PanicReason::CallsTraitMethod(fn_name),
                    _ => PanicReason::CallsMethodForNoMIR(fn_name),
                };

                fn_to_no_panic.insert(f, PanicSpec::MightPanic(reason));
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
                    assert!(
                        is_panic_or_abort_fn(tcx, f) || !tcx.is_mir_available(f),
                        "function {:?} has no call_graph entry but is neither a panic fn nor no-MIR",
                        tcx.def_path_str(f)
                    );
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

                // match entry {
                //     PanicSpec::MightPanic(PanicReason::ContainsPanic) => {
                //         // KEEP strongest reason — do not overwrite
                //     }
                //     PanicSpec::MightPanic(PanicReason::Unknown) => {
                //         *entry = PanicSpec::MightPanic(PanicReason::Transitive(bad_callees));
                //     }
                //     PanicSpec::MightPanic(PanicReason::Transitive(_)) => {
                //         *entry = PanicSpec::MightPanic(PanicReason::Transitive(bad_callees));
                //     }
                //     PanicSpec::MightPanic(PanicReason::CallsTraitMethod(_)) => {
                //         // TEMPORARY: treat CallsTraitMethod as WillNotPanic
                //         *entry = PanicSpec::WillNotPanic;
                //         changed = true;
                //     }
                //     PanicSpec::MightPanic(PanicReason::CallsMethodForNoMIR(_)) => {
                //         // KEEP stronger reason — do not overwrite
                //     }
                //     PanicSpec::WillNotPanic => unreachable!(),
                // }
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
