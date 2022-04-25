use std::cell::RefCell;

use liquid_rust_core::{desugar::Desugar, ty as core};
use liquid_rust_syntax::surface;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;

use crate::{
    lowering::LoweringCtxt,
    ty::{self, BaseTy, Sort},
};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
    pub adt_defs: core::AdtDefs,
    pub adt_defs_typeck: RefCell<FxHashMap<LocalDefId, ty::AdtDef>>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: FxHashMap<LocalDefId, ty::FnSpec>,
        adt_defs: core::AdtDefs,
    ) -> Self {
        GlobalEnv {
            fn_specs: RefCell::new(fn_specs),
            adt_defs,
            adt_defs_typeck: RefCell::new(FxHashMap::default()),
            tcx,
        }
    }

    pub fn lookup_fn_sig(&self, did: DefId) -> ty::Binders<ty::FnSig> {
        let local_def = did.as_local().unwrap();

        self.fn_specs
            .borrow_mut()
            .entry(local_def)
            .or_insert_with(|| {
                let fn_sig = surface::default_fn_sig(self.tcx, did);
                let fn_sig = Desugar::desugar_fn_sig(&self.adt_defs, fn_sig);
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
        let local_did = def_id.as_local().unwrap();
        self.adt_defs_typeck
            .borrow_mut()
            .entry(local_did)
            .or_insert_with(|| {
                let adt_def = self.adt_defs.get(local_did).unwrap();
                LoweringCtxt::lower_adt_def(adt_def)
            })
            .clone()
    }

    pub fn sorts(&self, bty: &BaseTy) -> Vec<Sort> {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => vec![Sort::int()],
            BaseTy::Bool => vec![Sort::bool()],
            BaseTy::Adt(def_id, _) => self.adt_def(*def_id).sorts(),
        }
    }
}
