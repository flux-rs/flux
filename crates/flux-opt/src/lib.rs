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

// NOTE by Andrew @ninehusky:
// I kind of want to push this through to the top-level flux attributes.
// The true/falseness of "no panic" gives me this double negation
// that I always mess up.
pub enum PanicSpec {
    WillNotPanic,
    MightPanic(PanicReason),
}

pub enum PanicReason {
    Unknown,
    Transitive(Vec<DefId>),
    CallsTraitMethod(String),
    CallsMethodForNoMIR(String),
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
                fn_to_no_panic
                    .insert(f, PanicSpec::MightPanic(PanicReason::Transitive(bad_callees)));
            }
        }
    }

    fn_to_no_panic
        .iter()
        .map(|(&k, v)| (k, matches!(v, PanicSpec::WillNotPanic)))
        .collect::<FxHashMap<DefId, bool>>()
}
