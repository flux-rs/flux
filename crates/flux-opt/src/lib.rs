#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use flux_common::bug;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::TerminatorKind,
    ty::{self, TyCtxt},
};

// NOTE by Andrew @ninehusky:
// I kind of want to push this through to the top-level flux attributes.
// The true/falseness of "no panic" gives me this double negation
// that I always mess up.
pub enum PanicSpec {
    MightPanic,
    WillNotPanic,
}

// should we bail?
fn has_unknown_callees(tcx: &TyCtxt, def_id: DefId) -> bool {
    let body = tcx.optimized_mir(def_id);

    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);
            if let ty::FnDef(def_id, _) = ty.kind() {
                if !tcx.is_mir_available(*def_id) {
                    return true;
                }
            }
        }
    }
    false
}

fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Vec<DefId> {
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
    let mut call_graph: FxHashMap<DefId, Vec<DefId>> = FxHashMap::default();
    let mut worklist: Vec<DefId> = vec![];

    // 1. Get the local functions; these are what we care about.
    for local in tcx.hir_body_owners() {
        let def_id = local.to_def_id();
        if tcx.def_kind(def_id).is_fn_like() {
            if tcx.is_mir_available(def_id) {
                fn_to_no_panic.insert(def_id, PanicSpec::MightPanic);
                call_graph.insert(def_id, get_callees(&tcx, def_id));
                worklist.push(def_id);
            } else {
                // If we don't have the MIR for a local function, something bad has happened.
                bug!("missing MIR for local function.");
            }
        }
    }

    // 2. Explore the call graph to find all reachable functions.
    while let Some(f) = worklist.pop() {
        let callees = call_graph.get(&f).unwrap().clone();
        for callee in callees {
            if !tcx.is_mir_available(callee) {
                // keep the "MightPanic" status if any callee is missing MIR.
                continue;
            }

            if !fn_to_no_panic.contains_key(&callee) {
                fn_to_no_panic.insert(callee, PanicSpec::MightPanic);
                call_graph.insert(callee, get_callees(&tcx, callee));
                worklist.push(callee);
            }
        }
    }

    // 3. Until a fixpoint is reached, mark functions as "WillNotPanic"
    //    if all their callees are "WillNotPanic".

    let mut changed = true;

    while changed {
        changed = false;

        let keys: Vec<DefId> = fn_to_no_panic.keys().copied().collect();
        for f in keys {
            let callees = call_graph.get(&f).unwrap().clone();
            let status = fn_to_no_panic.get(&f).unwrap();
            if matches!(status, PanicSpec::WillNotPanic) {
                continue;
            }
            let mut ok = true;

            for callee in callees {
                if !tcx.is_mir_available(callee) {
                    ok = false;
                    break;
                }

                match fn_to_no_panic.get(&callee) {
                    Some(PanicSpec::WillNotPanic) => {}
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                let status = fn_to_no_panic.get_mut(&f).unwrap();
                *status = PanicSpec::WillNotPanic;
                changed = true;
            }
        }
    }
    fn_to_no_panic
        .iter()
        .map(|(&k, v)| (k, matches!(v, PanicSpec::WillNotPanic)))
        .collect()
}
