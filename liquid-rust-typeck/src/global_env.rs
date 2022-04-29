use std::cell::RefCell;

use liquid_rust_common::config::{AssertBehaviorOptions, CONFIG};
use liquid_rust_core::{
    desugar,
    ty::{self as core, AdtSortsMap},
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
    adt_defs: FxHashMap<DefId, ty::AdtDef>,
    assert_behavior: AssertBehaviorOptions,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let assert_behavior = match CONFIG.default_assert_terminator_behavior {
            0 => AssertBehaviorOptions::Ignore,
            1 => AssertBehaviorOptions::Assume,
            2 => AssertBehaviorOptions::Check,
            _ => {
                unreachable!(
                    "unexpected default assert behavior {:?}",
                    CONFIG.default_assert_terminator_behavior
                )
            }
        };

        GlobalEnv {
            fn_sigs: RefCell::new(FxHashMap::default()),
            adt_sorts: FxHashMap::default(),
            adt_defs: FxHashMap::default(),
            tcx,
            assert_behavior,
        }
    }

    pub fn register_assert_behavior(&mut self, behavior: AssertBehaviorOptions) {
        self.assert_behavior = behavior;
    }

    pub fn register_adt_sorts(&mut self, def_id: DefId, sorts: Vec<core::Sort>) {
        self.adt_sorts.insert(def_id, sorts);
    }

    pub fn register_fn_sig(&mut self, def_id: DefId, fn_sig: core::FnSig) {
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig);
        self.fn_sigs.get_mut().insert(def_id, fn_sig);
    }

    pub fn register_adt_def(&mut self, def_id: DefId, adt_def: core::AdtDef) {
        let adt_def = LoweringCtxt::lower_adt_def(&adt_def);
        self.adt_defs.insert(def_id, adt_def);
    }

    pub fn lookup_fn_sig(&self, def_id: DefId) -> ty::PolySig {
        self.fn_sigs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let fn_sig = surface::default_fn_sig(self.tcx, def_id);
                let fn_sig = desugar::desugar_fn_sig(self.tcx.sess, self, fn_sig).unwrap();
                debug_assert!(Wf::new(self.tcx.sess, self).check_fn_sig(&fn_sig).is_ok());
                LoweringCtxt::lower_fn_sig(fn_sig)
            })
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

    pub fn assert_behavior(&self) -> &AssertBehaviorOptions {
        &self.assert_behavior
    }
}

impl AdtSortsMap for GlobalEnv<'_> {
    fn get(&self, def_id: DefId) -> Option<&[core::Sort]> {
        Some(self.adt_sorts.get(&def_id)?)
    }
}
