use std::cell::RefCell;

use flux_common::config::{AssertBehavior, CONFIG};
use flux_errors::FluxSession;
use itertools::Itertools;
use rustc_errors::FatalError;
use rustc_hash::FxHashMap;
use rustc_hir::{def_id::DefId, LangItem};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;
use rustc_span::Symbol;

use crate::{
    core::{self, VariantIdx},
    intern::List,
    rustc,
    ty::{self, fold::TypeFoldable, subst::BVarFolder, Binders},
};

#[derive(Debug)]
pub struct ConstInfo {
    pub def_id: DefId,
    pub sym: Symbol,
    pub val: i128,
}

pub struct GlobalEnv<'genv, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'genv FluxSession,
    fn_sigs: RefCell<FxHashMap<DefId, ty::PolySig>>,
    pub consts: Vec<ConstInfo>,
    adt_defs: RefCell<FxHashMap<DefId, ty::AdtDef>>,
    adt_variants: RefCell<FxHashMap<DefId, Option<Vec<ty::PolyVariant>>>>,
    check_asserts: AssertBehavior,
    /// Some functions can only to be called after all annotated adts have been
    /// registered. We use this flag to check at runtime that this is actually the
    /// case.
    adts_registered: bool,
}

impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'genv FluxSession) -> Self {
        let check_asserts = CONFIG.check_asserts;

        GlobalEnv {
            fn_sigs: RefCell::new(FxHashMap::default()),
            consts: vec![],
            adt_defs: RefCell::new(FxHashMap::default()),
            adt_variants: RefCell::new(FxHashMap::default()),
            tcx,
            sess,
            check_asserts,
            adts_registered: false,
        }
    }

    pub fn register_assert_behavior(&mut self, behavior: AssertBehavior) {
        self.check_asserts = behavior;
    }

    pub fn register_adt_def(&mut self, def_id: DefId, sorts: &[core::Sort]) {
        let sorts = sorts
            .iter()
            .map(|sort| ty::conv::conv_sort(*sort))
            .collect_vec();
        self.adt_defs
            .get_mut()
            .insert(def_id, ty::AdtDef::new(self.tcx.adt_def(def_id), sorts));
    }

    /// This function must be called after all adts are registered
    pub fn finish_adt_registration(&mut self) {
        self.adts_registered = true;
    }

    pub fn register_fn_sig(&mut self, def_id: DefId, fn_sig: core::FnSig) {
        let fn_sig = ty::conv::ConvCtxt::conv_fn_sig(self, fn_sig);
        self.fn_sigs.get_mut().insert(def_id, fn_sig);
    }

    pub fn register_struct_def(&mut self, def_id: DefId, struct_def: core::StructDef) {
        let (adt_def, variant) = ty::conv::ConvCtxt::conv_struct_def(self, &struct_def);
        let variants = variant.map(|variant_def| vec![variant_def]);
        self.adt_variants.get_mut().insert(def_id, variants);
        self.adt_defs.get_mut().insert(def_id, adt_def);
    }

    pub fn register_enum_def(&mut self, def_id: DefId, enum_def: core::EnumDef) {
        if let Some(variants) = ty::conv::ConvCtxt::conv_enum_def(self, enum_def) {
            // println!("TRACE: register_enum_def {def_id:?} {variants:?}");
            self.adt_variants.get_mut().insert(def_id, Some(variants));
        }

        let sorts = self.sorts_of(def_id);
        self.adt_defs
            .get_mut()
            .insert(def_id, ty::AdtDef::new(self.tcx.adt_def(def_id), sorts));
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
        debug_assert!(self.adts_registered);
        self.adt_defs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| ty::AdtDef::new(self.tcx.adt_def(def_id), vec![]))
            .clone()
    }

    pub fn mk_box(&self, ty: ty::Ty, alloc: ty::Ty) -> ty::Ty {
        let def_id = self.tcx.require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id);

        // this is harcoding that `Box` has two type parameters and
        // it is indexed by unit. We leave this as a reminder in case
        // that ever changes.
        debug_assert_eq!(self.generics_of(def_id).params.len(), 2);
        debug_assert!(adt_def.sorts().is_empty());

        let bty = ty::BaseTy::adt(adt_def, vec![ty, alloc]);
        ty::Ty::indexed(bty, vec![])
    }

    pub fn check_asserts(&self) -> &AssertBehavior {
        &self.check_asserts
    }

    pub fn variant_sig(&self, def_id: DefId, variant_idx: VariantIdx) -> ty::PolySig {
        // let sorts = self.sorts_of(def_id);
        let poly_variant = self.variant(def_id, variant_idx);
        let variant = poly_variant.skip_binders();
        let sorts = poly_variant.params();
        let sig = ty::FnSig::new(vec![], variant.fields.clone(), variant.ret.clone(), vec![]);
        ty::Binders::new(sig, sorts)
    }

    pub fn sorts_of(&self, def_id: DefId) -> List<ty::Sort> {
        self.adt_def(def_id).sorts().clone()
    }

    pub fn downcast(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
        substs: &[ty::Ty],
        exprs: &[ty::Expr],
    ) -> Vec<ty::Ty> {
        // TODO: self.variant(def_id, variant_idx).replace_bound_vars(exprs).replace_generic_types(substs).skip_binders().fields
        let variant = self.variant(def_id, variant_idx);

        // println!("TRACE: downcast {variant:?}");

        variant
            .skip_binders()
            .fields
            .iter()
            .map(|ty| {
                ty.fold_with(&mut BVarFolder::new(exprs))
                    .replace_generic_types(substs)
            })
            .collect()
    }

    fn variant(&self, def_id: DefId, variant_idx: VariantIdx) -> ty::PolyVariant {
        let def_id_variants = self.tcx.adt_def(def_id).variants();
        // println!("TRACE: variant: {def_id:?} at {variant_idx:?} {def_id_variants:?}");

        self.adt_variants
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                Some(
                    def_id_variants
                        .iter()
                        .map(|variant_def| self.default_variant_def(def_id, variant_def))
                        .collect(),
                )
            })
            .as_ref()
            .expect("cannot get variant of opaque struct")[variant_idx.as_usize()]
        .clone()
    }

    pub fn generics_of(&self, def_id: DefId) -> rustc::ty::Generics<'tcx> {
        rustc::lowering::lower_generics(self.tcx, self.tcx.generics_of(def_id))
            .unwrap_or_else(|_| FatalError.raise())
    }

    pub fn default_fn_sig(&self, def_id: DefId) -> ty::PolySig {
        match rustc::lowering::lower_fn_sig(self.tcx, self.tcx.fn_sig(def_id)) {
            Ok(fn_sig) => self.refine_fn_sig(&fn_sig, &mut |_| ty::Pred::tt()),
            Err(_) => FatalError.raise(),
        }
    }

    pub fn default_type_of(&self, def_id: DefId) -> ty::Ty {
        match rustc::lowering::lower_ty(self.tcx, self.tcx.type_of(def_id)) {
            Ok(rustc_ty) => self.refine_ty(&rustc_ty, &mut |_| ty::Pred::tt()),
            Err(_) => FatalError.raise(),
        }
    }

    fn default_variant_def(
        &self,
        adt_def_id: DefId,
        variant_def: &rustc_middle::ty::VariantDef,
    ) -> ty::PolyVariant {
        let fields = variant_def
            .fields
            .iter()
            .map(|field| self.default_type_of(field.did))
            .collect_vec();
        let ret = self.default_type_of(adt_def_id);

        Binders::new(ty::VariantDef::new(fields, ret), vec![])
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
        let sorts = bty.sorts();
        if sorts.is_empty() {
            ty::Ty::indexed(bty, vec![])
        } else {
            let pred = ty::Binders::new(mk_pred(sorts), sorts);
            ty::Ty::exists(bty, pred)
        }
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
