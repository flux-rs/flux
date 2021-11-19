use liquid_rust_core::ty::FnSig;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub struct GlobalEnv<'tcx> {
    pub sigs: FxHashMap<DefId, FnSig>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sigs: FxHashMap<DefId, FnSig>) -> Self {
        GlobalEnv { tcx, sigs }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &FnSig {
        &self.sigs[&did]
    }
}
