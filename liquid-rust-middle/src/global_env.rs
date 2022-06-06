use std::{cell::RefCell, iter};

use itertools::Itertools;
use liquid_rust_common::config::{AssertBehavior, CONFIG};
use liquid_rust_errors::LiquidRustSession;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;

use crate::{
    core::{self, VariantIdx},
    intern::List,
    rustc,
    ty::{self, fold::TypeFoldable},
};

pub struct GlobalEnv<'genv, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'genv LiquidRustSession,
    fn_sigs: RefCell<FxHashMap<DefId, ty::PolySig>>,
    adt_sorts: RefCell<FxHashMap<DefId, List<ty::Sort>>>,
    adt_defs: RefCell<FxHashMap<DefId, ty::AdtDef>>,
    adt_fields: RefCell<FxHashMap<DefId, ty::Ty>>,
    check_asserts: AssertBehavior,
}

impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'genv LiquidRustSession) -> Self {
        let check_asserts = CONFIG.check_asserts;

        GlobalEnv {
            fn_sigs: RefCell::new(FxHashMap::default()),
            adt_sorts: RefCell::new(FxHashMap::default()),
            adt_defs: RefCell::new(FxHashMap::default()),
            adt_fields: RefCell::new(FxHashMap::default()),
            tcx,
            sess,
            check_asserts,
        }
    }

    pub fn register_assert_behavior(&mut self, behavior: AssertBehavior) {
        self.check_asserts = behavior;
    }

    pub fn register_adt_sorts(&mut self, def_id: DefId, sorts: &[core::Sort]) {
        let sorts = sorts
            .iter()
            .map(|sort| ty::lowering::lower_sort(*sort))
            .collect();
        self.adt_sorts
            .get_mut()
            .insert(def_id, List::from_vec(sorts));
    }

    pub fn register_fn_sig(&mut self, def_id: DefId, fn_sig: core::FnSig) {
        let fn_sig = ty::lowering::LoweringCtxt::lower_fn_sig(self, fn_sig);
        self.fn_sigs.get_mut().insert(def_id, fn_sig);
    }

    pub fn register_adt_def(&mut self, def_id: DefId, adt_def: core::AdtDef) {
        let rust_adt_def = self.tcx.adt_def(def_id);
        let (mut cx, sorts) = ty::lowering::LoweringCtxt::from_adt_def(self, &adt_def);
        if let core::AdtDefKind::Transparent { variants: Some(variants) } = &adt_def.kind {
            for (variant, rust_variant) in iter::zip(variants, rust_adt_def.variants()) {
                if let Some(variant) = variant {
                    for (field_def, ty) in
                        iter::zip(&rust_variant.fields, cx.lower_variant_def(variant))
                    {
                        self.adt_fields.borrow_mut().insert(field_def.did, ty);
                    }
                }
            }
        }
        let adt_def = ty::lowering::lower_adt_def(self.tcx, &rust_adt_def, &sorts);
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

    fn field_ty(&self, adt_def_id: DefId, field_def_id: DefId) -> ty::Binders<ty::Ty> {
        let adt_def = self.adt_def(adt_def_id);
        let ty = self
            .adt_fields
            .borrow_mut()
            .entry(field_def_id)
            .or_insert_with(|| self.default_ty(field_def_id))
            .clone();
        ty::Binders::new(ty, adt_def.sorts().clone())
    }

    pub fn check_asserts(&self) -> &AssertBehavior {
        &self.check_asserts
    }

    pub fn variant_sig(&self, def_id: DefId, variant_idx: VariantIdx) -> ty::PolySig {
        let adt_def = self.adt_def(def_id);
        let variant = &adt_def.variants().unwrap()[variant_idx];
        let args = variant
            .fields
            .iter()
            .map(|field_def_id| self.field_ty(def_id, *field_def_id).skip_binders().clone())
            .collect_vec();

        let substs = adt_def
            .generics()
            .iter()
            .map(|p| ty::Ty::param(*p))
            .collect_vec();

        let bty = ty::BaseTy::adt(adt_def.clone(), substs);

        let indices = (0..adt_def.sorts().len())
            .map(|idx| ty::Expr::bvar(ty::BoundVar::innermost(idx)).into())
            .collect_vec();
        let ret = ty::Ty::indexed(bty, indices);
        let sig = ty::FnSig::new(vec![], args, ret, vec![]);
        ty::Binders::new(sig, adt_def.sorts().clone())
    }

    pub fn sorts_of(&self, def_id: DefId) -> List<ty::Sort> {
        self.adt_sorts
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| List::from_vec(vec![]))
            .clone()
    }

    pub fn downcast(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
        substs: &[ty::Ty],
        exprs: &[ty::Expr],
    ) -> Vec<ty::Ty> {
        let adt_def = self.adt_def(def_id);
        adt_def
            .variant(variant_idx)
            .expect("cannot downcast opaque adt")
            .fields
            .iter()
            .map(|field_def_id| {
                self.field_ty(def_id, *field_def_id)
                    .replace_bound_vars(exprs)
                    .replace_generic_types(substs)
            })
            .collect()
    }

    pub fn default_fn_sig(&self, def_id: DefId) -> ty::PolySig {
        let fn_sig = rustc::lowering::lower_fn_sig(self.tcx, self.tcx.fn_sig(def_id));
        self.tcx.sess.abort_if_errors();
        self.refine_fn_sig(&fn_sig.unwrap(), &mut |_| ty::Pred::tt())
    }

    pub fn default_adt_def(&self, def_id: DefId) -> ty::AdtDef {
        let adt_def = self.tcx.adt_def(def_id);
        ty::lowering::lower_adt_def(self.tcx, &adt_def, &[])
    }

    pub fn adt_def_generics(&self, def_id: DefId) -> Vec<rustc_middle::ty::ParamTy> {
        let generics = self
            .tcx
            .generics_of(def_id)
            .params
            .iter()
            .map(|p| rustc_middle::ty::ParamTy { index: p.index, name: p.name })
            .collect_vec();
        generics
    }

    fn default_ty(&self, def_id: DefId) -> ty::Ty {
        let rust_ty = rustc::lowering::lower_ty(self.tcx, self.tcx.type_of(def_id));
        self.tcx.sess.abort_if_errors();
        self.refine_ty(&rust_ty.unwrap(), &mut |_| ty::Pred::tt())
    }

    pub fn default_variant_def(
        &self,
        variant_def: &rustc_middle::ty::VariantDef,
    ) -> ty::VariantDef {
        let fields = variant_def
            .fields
            .iter()
            .map(|field| field.did)
            .collect_vec();

        ty::VariantDef::new(fields)
    }

    pub fn refine_fn_sig(
        &self,
        fn_sig: &rustc::ty::FnSig,
        mk_pred: &mut impl FnMut(&[ty::Sort]) -> ty::Pred,
    ) -> ty::PolySig {
        let args = fn_sig
            .inputs()
            .iter()
            .map(|ty| self.refine_ty(ty, mk_pred))
            .collect_vec();
        let ret = self.refine_ty(&fn_sig.output(), mk_pred);
        ty::PolySig::new(ty::FnSig::new(vec![], args, ret, vec![]), vec![])
    }

    pub fn refine_ty(
        &self,
        ty: &rustc::ty::Ty,
        mk_pred: &mut impl FnMut(&[ty::Sort]) -> ty::Pred,
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
                ty::BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Bool => ty::BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
        };
        let pred = ty::Binders::new(mk_pred(bty.sorts()), bty.sorts());
        ty::Ty::exists(bty, pred)
    }

    pub fn refine_generic_arg(
        &self,
        ty: &rustc::ty::GenericArg,
        mk_pred: &mut impl FnMut(&[ty::Sort]) -> ty::Pred,
    ) -> ty::Ty {
        match ty {
            rustc::ty::GenericArg::Ty(ty) => self.refine_ty(ty, mk_pred),
        }
    }
}
