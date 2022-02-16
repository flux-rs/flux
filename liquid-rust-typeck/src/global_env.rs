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
    pub adt_defs: AdtDefs,
    pub tcx: TyCtxt<'tcx>,
}

pub struct AdtDefs {
    map: FxHashMap<LocalDefId, ty::AdtDef>,
}

impl AdtDefs {
    pub fn new(adt_defs: FxHashMap<LocalDefId, ty::AdtDef>) -> Self {
        Self { map: adt_defs }
    }
}

#[derive(Debug)]
pub struct Qualifiers {
    qualifs: Vec<core::Qualifier>,
}

impl Qualifiers {
    pub fn new(qualifs: Vec<core::Qualifier>) -> Self {
        Self { qualifs }
    }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: FxHashMap<LocalDefId, FnSpec>,
        adt_defs: AdtDefs,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> &core::FnSig {
        &self.fn_specs[&did.as_local().unwrap()].fn_sig
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn sort(&self, bty: &BaseTy) -> Sort {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => Sort::int(),
            BaseTy::Bool => Sort::bool(),
            BaseTy::Adt(def_id, _) => {
                if let Some(def) = self.adt_defs.get(*def_id) {
                    Sort::tuple(def.refined_by.iter().map(|(_, sort)| sort.clone()))
                } else {
                    Sort::unit()
                }
            }
        }
    }
}

impl AdtDefs {
    pub fn get(&self, did: DefId) -> Option<&ty::AdtDef> {
        self.map.get(&did.as_local()?)
    }
}

impl FromIterator<(LocalDefId, core::AdtDef)> for AdtDefs {
    fn from_iter<T: IntoIterator<Item = (LocalDefId, core::AdtDef)>>(iter: T) -> Self {
        AdtDefs {
            map: iter
                .into_iter()
                .map(|(did, def)| (did, lower_adt_def(def)))
                .collect(),
        }
    }
}
