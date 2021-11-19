use liquid_rust_core::ty::FnSig;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub struct FnSpec {
    pub fn_sig: FnSig,
    pub assume: bool,
}

pub struct GlobalEnv<'tcx> {
    pub specs: FxHashMap<DefId, FnSpec>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: FxHashMap<DefId, FnSpec>) -> Self {
        GlobalEnv { tcx, specs }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &FnSig {
        &self.specs[&did].fn_sig
    }
}
