use std::cell::RefCell;

use liquid_rust_core::{
    desugar,
    ty::{self as core, RefinedByMap},
};
use liquid_rust_syntax::surface;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;

use crate::{
    lowering::LoweringCtxt,
    ty::{self, BaseTy, Sort},
    wf::Wf,
};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: RefCell<FxHashMap<DefId, ty::FnSpec>>,
    refined_by: FxHashMap<DefId, Vec<core::Param>>,
    adt_defs: FxHashMap<DefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        GlobalEnv {
            fn_specs: RefCell::new(FxHashMap::default()),
            refined_by: FxHashMap::default(),
            adt_defs: FxHashMap::default(),
            tcx,
        }
    }

    pub fn register_refined_by(&mut self, def_id: DefId, params: Vec<core::Param>) {
        self.refined_by.insert(def_id, params);
    }

    pub fn register_fn_spec(&mut self, def_id: DefId, spec: core::FnSpec) {
        let fn_sig = LoweringCtxt::lower_fn_sig(spec.fn_sig);
        let spec = ty::FnSpec { fn_sig, assume: spec.assume };
        self.fn_specs.get_mut().insert(def_id, spec);
    }

    pub fn register_adt_def(&mut self, def_id: DefId, adt_def: core::AdtDef) {
        let adt_def = LoweringCtxt::lower_adt_def(&adt_def);
        self.adt_defs.insert(def_id, adt_def);
    }

    pub fn lookup_fn_sig(&self, def_id: DefId) -> ty::Binders<ty::FnSig> {
        self.fn_specs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let fn_sig = surface::default_fn_sig(self.tcx, def_id);
                let fn_sig = desugar::desugar_fn_sig(self.tcx.sess, self, fn_sig).unwrap();
                debug_assert!(Wf::new(self.tcx.sess, self).check_fn_sig(&fn_sig).is_ok());
                let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig);
                ty::FnSpec { fn_sig, assume: true }
            })
            .fn_sig
            .clone()
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, def_id: DefId) -> ty::AdtDef {
        self.adt_defs[&def_id].clone()
    }

    pub fn sorts(&self, bty: &BaseTy) -> Vec<Sort> {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => vec![Sort::int()],
            BaseTy::Bool => vec![Sort::bool()],
            BaseTy::Adt(def_id, _) => self.adt_def(*def_id).sorts(),
        }
    }
}

impl RefinedByMap for GlobalEnv<'_> {
    fn get(&self, def_id: DefId) -> Option<&[core::Param]> {
        Some(self.refined_by.get(&def_id)?)
    }
}
