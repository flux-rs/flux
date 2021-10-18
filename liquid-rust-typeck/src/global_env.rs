use liquid_rust_core::ty::FnSig;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

pub struct GlobalEnv {
    pub sigs: FxHashMap<DefId, FnSig>,
}

impl GlobalEnv {
    pub fn new(sigs: FxHashMap<DefId, FnSig>) -> Self {
        Self { sigs }
    }
}
