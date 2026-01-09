#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use flux_middle::global_env::GlobalEnv;
use rustc_hash::FxHashMap;
use rustc_middle::{mir::TerminatorKind, ty};
use rustc_span::def_id::DefId;

fn get_callees(genv: &GlobalEnv, def_id: DefId) -> Vec<DefId> {
    let body = genv.tcx().optimized_mir(def_id);

    let mut callees = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, genv.tcx());
            if let ty::FnDef(def_id, _) = ty.kind() {
                callees.push(*def_id)
            }
        }
    }
    callees
}

// Invariant: the DefIds in the returned map are all LocalDefIds
pub fn infer_no_panics(genv: GlobalEnv) -> FxHashMap<DefId, bool> {
    let tcx = genv.tcx();

    let mut fn_to_no_panic: FxHashMap<DefId, bool> = FxHashMap::default();
    let mut call_graph: FxHashMap<DefId, Vec<DefId>> = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id).is_fn_like() {
            let def_id = def_id.to_def_id();
            // Conservatively assume functions will panic
            fn_to_no_panic.insert(def_id, false);
            let callees = get_callees(&genv, def_id);
            call_graph.insert(def_id, callees);
        }
    }

    let mut changed = true;
    let keys = fn_to_no_panic.keys().cloned().collect::<Vec<_>>();
    while changed {
        changed = false;

        for f in &keys {
            if fn_to_no_panic[f] {
                continue;
            }

            let callees = &call_graph[f];

            let mut ok = true;
            for callee in callees {
                let Some(_) = callee.as_local() else {
                    ok = false;
                    break;
                };

                if !fn_to_no_panic.get(callee).copied().unwrap_or(false) {
                    ok = false;
                    break;
                }
            }

            if ok {
                *fn_to_no_panic.get_mut(f).unwrap() = true;
                changed = true;
            }
        }
    }
    fn_to_no_panic
}
