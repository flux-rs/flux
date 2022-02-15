use liquid_rust_core::ty::FnSig;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;

use crate::ty::{BaseTy, Sort};

pub struct FnSpec {
    pub fn_sig: FnSig,
    pub assume: bool,
}

pub struct GlobalEnv<'tcx> {
    pub specs: FxHashMap<LocalDefId, FnSpec>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, specs: FxHashMap<LocalDefId, FnSpec>) -> Self {
        GlobalEnv { tcx, specs }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &FnSig {
        &self.specs[&did.as_local().unwrap()].fn_sig
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn sort(&self, bty: &BaseTy) -> Sort {
        match bty {
            BaseTy::Int(_) => Sort::int(),
            BaseTy::Uint(_) => Sort::int(),
            BaseTy::Bool => Sort::bool(),
            BaseTy::Adt(_, _) => Sort::int(),
        }
    }
}
