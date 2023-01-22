use rustc_hir::def_id::DefId;

use crate::rty;

pub trait CrateStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::PolySig>;
}

pub type CrateStoreDyn = dyn CrateStore;
