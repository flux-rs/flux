#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use std::collections::HashSet;

use flux_common::bug;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};

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
    Transitive(Vec<DefId>),
    CallsTraitMethod(String),
    CallsMethodForNoMIR(String),
}

pub(crate) fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Vec<DefId> {
    let body = tcx.optimized_mir(def_id);

    let mut callees = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);
            if let ty::FnDef(def_id, _) = ty.kind() {
                callees.push(*def_id);
            }
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
            if tcx.is_mir_available(callee) {
                if !fn_to_no_panic.contains_key(&callee) {
                    fn_to_no_panic.insert(callee, PanicSpec::MightPanic(PanicReason::Unknown));
                    call_graph.insert(callee, get_callees(&tcx, callee));
                    worklist.push(callee);
                }
            } else {
                // Missing MIR: record *why* f cannot be proven no-panic
                let fn_name = tcx.def_path_str(callee);

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

            let callees = call_graph.get(&f).unwrap();

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

    println!("Hey! our no-panic analysis finished!");
    println!("um... hm. well, here's what we found.");
    println!("well, there were {} functions analyzed.", fn_to_no_panic.len());
    println!("that's for sure.");
    // map reasons to count.
    let mut reasons_to_count: FxHashMap<String, usize> = FxHashMap::default();
    for (k, v) in &fn_to_no_panic {
        let reason = match v {
            PanicSpec::WillNotPanic => "WILL NOT PANIC".to_string(),
            PanicSpec::MightPanic(reason) => {
                match reason {
                    PanicReason::Unknown => "MIGHT PANIC: unknown reason".to_string(),
                    PanicReason::Transitive(_) => "MIGHT PANIC: transitive".to_string(),
                    PanicReason::CallsTraitMethod(_) => {
                        "MIGHT PANIC: calls trait method".to_string()
                    }
                    PanicReason::CallsMethodForNoMIR(_) => {
                        "MIGHT PANIC: calls method with no MIR".to_string()
                    }
                }
            }
        };
        *reasons_to_count.entry(reason).or_insert(0) += 1;

        // match v {
        //     PanicSpec::WillNotPanic => {}
        //     PanicSpec::MightPanic(reason) => {
        //         match reason {
        //             PanicReason::Unknown => {
        //                 println!("  {}: MIGHT PANIC (unknown reason)", tcx.def_path_str(*k));
        //             }
        //             PanicReason::Transitive(bad_callees) => {
        //                 let callee_names: Vec<String> = bad_callees
        //                     .iter()
        //                     .map(|cid| tcx.def_path_str(*cid))
        //                     .collect();
        //                 println!(
        //                     "  {}: MIGHT PANIC (calls functions that might panic: {})",
        //                     tcx.def_path_str(*k),
        //                     callee_names.join(", ")
        //                 );
        //             }
        //             PanicReason::CallsTraitMethod(fn_name) => {
        //                 println!(
        //                     "  {}: MIGHT PANIC (calls trait method: {})",
        //                     tcx.def_path_str(*k),
        //                     fn_name
        //                 );
        //             }
        //             PanicReason::CallsMethodForNoMIR(fn_name) => {
        //                 println!(
        //                     "  {}: MIGHT PANIC (calls method with no MIR: {})",
        //                     tcx.def_path_str(*k),
        //                     fn_name
        //                 );
        //             }
        //         }
        //     }
        // }
    }

    for (reason, count) in reasons_to_count {
        println!("  {}: {}", reason, count);
    }

    visualize::visualize(&tcx, call_graph, "button.rs", &fn_to_no_panic);

    fn_to_no_panic
        .iter()
        .map(|(&k, v)| (k, matches!(v, PanicSpec::WillNotPanic)))
        .collect::<FxHashMap<DefId, bool>>()
}
