use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;

use crate::{
    lowering::lower_adt_def,
    ty::{self, BaseTy, Sort},
};

pub struct FnSpec {
    pub fn_sig: core::FnSig,
    pub assume: bool,
}

pub struct GlobalEnv<'tcx> {
    pub fn_specs: FxHashMap<LocalDefId, FnSpec>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: FxHashMap<LocalDefId, FnSpec>,
        adt_defs: Vec<(LocalDefId, core::AdtDef)>,
    ) -> Self {
        GlobalEnv {
            tcx,
            fn_specs,
            adt_defs: adt_defs
                .into_iter()
                .map(|(def_id, def)| (def_id, lower_adt_def(def)))
                .collect(),
        }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &core::FnSig {
        &self.fn_specs[&did.as_local().unwrap()].fn_sig
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn sort(&self, bty: &BaseTy) -> Sort {
        match bty {
            BaseTy::Int(_) => Sort::int(),
            BaseTy::Uint(_) => Sort::int(),
            BaseTy::Bool => Sort::bool(),
            BaseTy::Adt(def_id, _) => {
                if let Some(def) = self.adt_defs.get(&def_id.as_local().unwrap()) {
                    Sort::tuple(def.refined_by.iter().map(|(_, sort)| sort.clone()))
                } else {
                    Sort::unit()
                }
            }
        }
    }
}
