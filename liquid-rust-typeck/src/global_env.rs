use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;

use crate::ty::{self, BaseTy, Sort};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: FxHashMap<LocalDefId, ty::FnSpec>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: FxHashMap<LocalDefId, ty::FnSpec>,
        adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &ty::Binders<ty::FnSig> {
        &self.fn_specs[&did.as_local().unwrap()].fn_sig
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, did: DefId) -> &ty::AdtDef {
        &self.adt_defs[&did.as_local().unwrap()]
    }

    pub fn sort(&self, bty: &BaseTy) -> Sort {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => Sort::int(),
            BaseTy::Bool => Sort::bool(),
            BaseTy::Adt(def_id, _) => {
                if let Some(def) = def_id.as_local().and_then(|did| self.adt_defs.get(&did)) {
                    Sort::tuple(def.refined_by().iter().map(|param| param.sort.clone()))
                } else {
                    Sort::unit()
                }
            }
        }
    }
}
