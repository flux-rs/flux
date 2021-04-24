use std::collections::HashMap;

use liquid_rust_lrir::ty::FnSig;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, TyCtxt};

pub struct GlobalEnv<'tcx> {
    _tcx: TyCtxt<'tcx>,
    pub sigs: HashMap<DefId, FnSig>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(_tcx: TyCtxt<'tcx>, sigs: HashMap<DefId, FnSig>) -> Self {
        Self { _tcx, sigs }
    }

    pub fn fn_sig(&self, def_id: DefId, _substs: SubstsRef<'tcx>) -> &FnSig {
        &self.sigs[&def_id]
    }
}
