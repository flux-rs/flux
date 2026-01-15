#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::TerminatorKind,
    ty::{self, TyCtxt},
};

fn has_external_callees(tcx: &TyCtxt, def_id: LocalDefId) -> bool {
    let body = tcx.optimized_mir(def_id);

    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);
            if let ty::FnDef(def_id, _) = ty.kind() {
                if !def_id.is_local() {
                    return true;
                }
            }
        }
    }
    false
}

fn get_callees(tcx: &TyCtxt, def_id: LocalDefId) -> Vec<LocalDefId> {
    let body = tcx.optimized_mir(def_id);

    let mut callees = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let ty = func.ty(&body.local_decls, *tcx);
            if let ty::FnDef(def_id, _) = ty.kind() {
                if def_id.is_local() {
                    callees.push(def_id.as_local().unwrap());
                }
            }
        }
    }
    callees
}

pub fn infer_no_panics(tcx: TyCtxt) -> FxHashMap<LocalDefId, bool> {
    let mut fn_to_no_panic: FxHashMap<LocalDefId, bool> = FxHashMap::default();
    let mut call_graph: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id).is_fn_like() {
            // Conservatively assume functions will panic
            fn_to_no_panic.insert(def_id, false);
            let callees = get_callees(&tcx, def_id);
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
                if !fn_to_no_panic.get(callee).copied().unwrap_or(false) {
                    ok = false;
                    break;
                }
            }

            if has_external_callees(&tcx, *f) {
                ok = false;
            }

            if ok {
                *fn_to_no_panic.get_mut(f).unwrap() = true;
                changed = true;
            }
        }
    }
    fn_to_no_panic
}
