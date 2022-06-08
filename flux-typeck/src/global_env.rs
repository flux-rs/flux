use std::cell::RefCell;

use flux_common::config::{AssertBehavior, CONFIG};
use flux_middle::{
    core::{self, AdtSortsMap, VariantIdx},
    rustc,
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;

use crate::{
    lowering::LoweringCtxt,
    ty::{self, BaseTy, Sort},
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
            .or_insert_with(|| self.default_fn_sig(def_id))
            .clone()
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, def_id: DefId) -> ty::AdtDef {
        self.adt_defs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| self.default_adt_def(def_id))
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

    pub fn default_fn_sig(&self, def_id: DefId) -> ty::PolySig {
        let fn_sig = rustc::lowering::lower_fn_sig(self.tcx, self.tcx.fn_sig(def_id));
        self.tcx.sess.abort_if_errors();
        self.refine_fn_sig(&fn_sig.unwrap(), &mut |_| ty::Pred::tt())
    }

    pub fn default_adt_def(&self, def_id: DefId) -> ty::AdtDef {
        let adt_def = self.tcx.adt_def(def_id);
        let variants = adt_def
            .variants
            .iter()
            .map(|variant| self.default_variant_def(variant))
            .collect();
        ty::AdtDef::transparent(adt_def.did, vec![], variants)
    }

    pub fn default_variant_def(
        &self,
        variant_def: &rustc_middle::ty::VariantDef,
    ) -> ty::VariantDef {
        let fields = variant_def
            .fields
            .iter()
            .map(|field| {
                let ty = self.tcx.type_of(field.did);
                let ty = rustc::lowering::lower_ty(self.tcx, ty);
                self.tcx.sess.abort_if_errors();
                self.refine_ty(&ty.unwrap(), &mut |_| ty::Pred::tt())
            })
            .collect();
        ty::VariantDef { fields }
    }

    pub fn refine_fn_sig(
        &self,
        fn_sig: &rustc::ty::FnSig,
        mk_pred: &mut impl FnMut(&BaseTy) -> ty::Pred,
    ) -> ty::PolySig {
        let args = fn_sig
            .inputs()
            .iter()
            .map(|ty| self.refine_ty(ty, mk_pred))
            .collect_vec();
        let ret = self.refine_ty(&fn_sig.output(), mk_pred);
        ty::PolySig::new(vec![], ty::FnSig::new(vec![], args, ret, vec![]))
    }

    pub fn refine_ty(
        &self,
        ty: &rustc::ty::Ty,
        mk_pred: &mut impl FnMut(&BaseTy) -> ty::Pred,
    ) -> ty::Ty {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Never => return ty::Ty::never(),
            rustc::ty::TyKind::Param(param_ty) => return ty::Ty::param(*param_ty),
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Mut) => {
                return ty::Ty::mk_ref(ty::RefKind::Mut, self.refine_ty(ty, mk_pred));
            }
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Not) => {
                return ty::Ty::mk_ref(ty::RefKind::Shr, self.refine_ty(ty, mk_pred));
            }
            rustc::ty::TyKind::Float(float_ty) => return ty::Ty::float(*float_ty),
            rustc::ty::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.refine_ty(ty, mk_pred))
                    .collect_vec();
                return ty::Ty::tuple(tys);
            }
            rustc::ty::TyKind::Adt(def_id, substs) => {
                let adt_def = self.adt_def(*def_id);
                let substs = substs
                    .iter()
                    .map(|arg| self.refine_generic_arg(arg, mk_pred))
                    .collect_vec();
                BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Bool => BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => BaseTy::Uint(*uint_ty),
        };
        let pred = mk_pred(&bty);
        ty::Ty::exists(bty, pred)
    }

    pub fn refine_generic_arg(
        &self,
        ty: &rustc::ty::GenericArg,
        mk_pred: &mut impl FnMut(&BaseTy) -> ty::Pred,
    ) -> ty::Ty {
        match ty {
            rustc::ty::GenericArg::Ty(ty) => self.refine_ty(ty, mk_pred),
        }
    }
}

impl AdtSortsMap for GlobalEnv<'_> {
    fn get(&self, def_id: DefId) -> Option<&[core::Sort]> {
        Some(self.adt_sorts.get(&def_id)?)
    }
}
