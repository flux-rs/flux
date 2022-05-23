use std::cell::RefCell;

use itertools::Itertools;
use liquid_rust_common::config::{AssertBehavior, CONFIG};
use liquid_rust_core::{
    desugar,
    ty::{self as core, AdtSortsMap, VariantIdx},
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
    pub tcx: TyCtxt<'tcx>,
    fn_sigs: RefCell<FxHashMap<DefId, ty::PolySig>>,
    adt_sorts: FxHashMap<DefId, Vec<core::Sort>>,
    adt_defs: RefCell<FxHashMap<DefId, ty::AdtDef>>,
    check_asserts: AssertBehavior,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let check_asserts = CONFIG.check_asserts;

        GlobalEnv {
            fn_sigs: RefCell::new(FxHashMap::default()),
            adt_sorts: FxHashMap::default(),
            adt_defs: RefCell::new(FxHashMap::default()),
            tcx,
            check_asserts,
        }
    }

    pub fn register_assert_behavior(&mut self, behavior: AssertBehavior) {
        self.check_asserts = behavior;
    }

    pub fn register_adt_sorts(&mut self, def_id: DefId, sorts: Vec<core::Sort>) {
        self.adt_sorts.insert(def_id, sorts);
    }

    pub fn register_fn_sig(&mut self, def_id: DefId, fn_sig: core::FnSig) {
        let fn_sig = LoweringCtxt::lower_fn_sig(self, fn_sig);
        self.fn_sigs.get_mut().insert(def_id, fn_sig);
    }

    pub fn register_adt_def(&mut self, def_id: DefId, adt_def: core::AdtDef) {
        let adt_def = LoweringCtxt::lower_adt_def(self, &adt_def);
        self.adt_defs.get_mut().insert(def_id, adt_def);
    }

    pub fn lookup_fn_sig(&self, def_id: DefId) -> ty::PolySig {
        self.fn_sigs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let fn_sig = surface::default_fn_sig(self.tcx, def_id);
                let fn_sig = desugar::desugar_fn_sig(self.tcx.sess, self, fn_sig).unwrap();
                debug_assert!(Wf::new(self.tcx.sess, self).check_fn_sig(&fn_sig).is_ok());
                LoweringCtxt::lower_fn_sig(self, fn_sig)
            })
            .clone()
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, def_id: DefId) -> ty::AdtDef {
        self.adt_defs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let adt_def = core::AdtDef::default(self.tcx, self.tcx.adt_def(def_id));
                LoweringCtxt::lower_adt_def(self, &adt_def)
            })
            .clone()
    }

    pub fn sorts(&self, bty: &BaseTy) -> Vec<Sort> {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => vec![Sort::int()],
            BaseTy::Bool => vec![Sort::bool()],
            BaseTy::Adt(adt_def, _) => adt_def.sorts(),
        }
    }

    pub fn check_asserts(&self) -> &AssertBehavior {
        &self.check_asserts
    }

    pub fn variant_sig(&self, def_id: DefId, variant_idx: VariantIdx) -> ty::PolySig {
        let adt_def = self.adt_def(def_id);
        let variant = &adt_def.variants().unwrap()[variant_idx];
        let args = &variant.fields[..];
        // TODO(nilehmann) get generics from somewhere
        // TODO(nilehmann) we should store the return type in the variant
        let bty = BaseTy::adt(adt_def.clone(), vec![]);
        let exprs = adt_def
            .refined_by()
            .iter()
            .map(|param| ty::Expr::var(param.name))
            .collect_vec();
        let ret = ty::Ty::indexed(bty, exprs);
        let sig = ty::FnSig::new(vec![], args, ret, vec![]);
        ty::Binders::new(adt_def.refined_by(), sig)
    }
}

impl AdtSortsMap for GlobalEnv<'_> {
    fn get(&self, def_id: DefId) -> Option<&[core::Sort]> {
        Some(self.adt_sorts.get(&def_id)?)
    }
}
