use std::{cell::RefCell, collections::hash_map};

use flux_common::config::{AssertBehavior, CONFIG};
use flux_errors::FluxSession;
use itertools::Itertools;
use rustc_errors::FatalError;
use rustc_hash::FxHashMap;
use rustc_hir::{def_id::DefId, LangItem};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;

pub use crate::rustc::lowering::UnsupportedFnSig;
use crate::{
    fhir::{self, VariantIdx},
    intern::List,
    rty::{self, Binders},
    rustc,
};

#[derive(Debug)]
pub struct OpaqueStructErr(pub DefId);

pub struct GlobalEnv<'genv, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'genv FluxSession,
    pub qualifiers: Vec<rty::Qualifier>,
    fn_sigs: RefCell<FxHashMap<DefId, rty::PolySig>>,
    map: fhir::Map,
    adt_defs: RefCell<FxHashMap<DefId, rty::AdtDef>>,
    adt_variants: RefCell<FxHashMap<DefId, Option<Vec<rty::PolyVariant>>>>,
    check_asserts: AssertBehavior,
}

impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'genv FluxSession, map: fhir::Map) -> Self {
        let check_asserts = CONFIG.check_asserts;

        let mut adt_defs = FxHashMap::default();
        for adt_def in map.adts() {
            let adt_def = rty::conv::conv_adt_def(tcx, adt_def);
            adt_defs.insert(adt_def.def_id(), adt_def);
        }

        let mut qualifiers = vec![];
        for qualifier in map.qualifiers() {
            qualifiers.push(rty::conv::ConvCtxt::conv_qualifier(qualifier));
        }

        let mut genv = GlobalEnv {
            fn_sigs: RefCell::new(FxHashMap::default()),
            adt_defs: RefCell::new(adt_defs),
            adt_variants: RefCell::new(FxHashMap::default()),
            qualifiers,
            tcx,
            sess,
            check_asserts,
            map,
        };
        genv.register_struct_def_variants();
        genv.register_enum_def_variants();
        genv.register_fn_sigs();

        genv
    }

    fn register_struct_def_variants(&mut self) {
        for struct_def in self.map.structs() {
            let def_id = struct_def.def_id;
            let refined_by = &self.map().refined_by(struct_def.def_id).unwrap().params;
            let variant =
                rty::conv::ConvCtxt::conv_struct_def_variant(self, refined_by, struct_def);
            let variants = variant.map(|variant_def| vec![variant_def]);
            self.adt_variants.get_mut().insert(def_id, variants);
        }
    }

    fn register_enum_def_variants(&mut self) {
        for enum_def in self.map.enums() {
            let def_id = enum_def.def_id;
            if let Some(variants) = rty::conv::ConvCtxt::conv_enum_def_variants(self, enum_def) {
                self.adt_variants.get_mut().insert(def_id, Some(variants));
            }
        }
    }

    fn register_fn_sigs(&mut self) {
        for (def_id, fn_sig) in self.map.fn_sigs() {
            let fn_sig = rty::conv::ConvCtxt::conv_fn_sig(self, fn_sig);
            self.fn_sigs.get_mut().insert(def_id, fn_sig);
        }
    }

    pub fn map(&self) -> &fhir::Map {
        &self.map
    }

    pub fn register_assert_behavior(&mut self, behavior: AssertBehavior) {
        self.check_asserts = behavior;
    }

    pub fn lookup_fn_sig(&self, def_id: DefId) -> Result<rty::PolySig, UnsupportedFnSig> {
        match self.fn_sigs.borrow_mut().entry(def_id) {
            hash_map::Entry::Occupied(entry) => Ok(entry.get().clone()),
            hash_map::Entry::Vacant(entry) => {
                Ok(entry.insert(self.default_fn_sig(def_id)?).clone())
            }
        }
    }

    fn default_fn_sig(&self, def_id: DefId) -> Result<rty::PolySig, UnsupportedFnSig> {
        let fn_sig = rustc::lowering::lower_fn_sig_of(self.tcx, def_id)?.skip_binder();
        Ok(self.refine_fn_sig(&fn_sig, &mut |sorts| Binders::new(rty::Pred::tt(), sorts)))
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, def_id: DefId) -> rty::AdtDef {
        self.adt_defs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| rty::AdtDef::new(self.tcx.adt_def(def_id), vec![], vec![], false))
            .clone()
    }

    pub fn mk_box(&self, ty: rty::Ty, alloc: rty::Ty) -> rty::Ty {
        let def_id = self.tcx.require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id);

        // this is harcoding that `Box` has two type parameters and
        // it is indexed by unit. We leave this as a reminder in case
        // that ever changes.
        debug_assert_eq!(self.generics_of(def_id).params.len(), 2);
        debug_assert!(adt_def.sorts().is_empty());

        let bty =
            rty::BaseTy::adt(adt_def, vec![rty::GenericArg::Ty(ty), rty::GenericArg::Ty(alloc)]);
        rty::Ty::indexed(bty, rty::RefineArgs::empty())
    }

    pub fn check_asserts(&self) -> &AssertBehavior {
        &self.check_asserts
    }

    pub fn variant_sig(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> Result<rty::PolySig, OpaqueStructErr> {
        let poly_variant = self.variant(def_id, variant_idx)?;
        let variant = poly_variant.as_ref().skip_binders();
        let sorts = poly_variant.params();
        let sig = rty::FnSig::new(vec![], variant.fields.clone(), variant.ret.to_ty(), vec![]);
        Ok(rty::Binders::new(sig, sorts))
    }

    pub fn variant(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> Result<rty::PolyVariant, OpaqueStructErr> {
        Ok(self
            .adt_variants
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                Some(
                    self.tcx
                        .adt_def(def_id)
                        .variants()
                        .iter()
                        .map(|variant_def| self.default_variant_def(def_id, variant_def))
                        .collect(),
                )
            })
            .as_ref()
            .ok_or(OpaqueStructErr(def_id))?[variant_idx.as_usize()]
        .clone())
    }

    pub fn generics_of(&self, def_id: DefId) -> rustc::ty::Generics<'tcx> {
        rustc::lowering::lower_generics(self.tcx, self.sess, self.tcx.generics_of(def_id))
            .unwrap_or_else(|_| FatalError.raise())
    }

    fn refine_ty_true(&self, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        self.refine_ty(rustc_ty, &mut |sorts| Binders::new(rty::Pred::tt(), sorts))
    }

    pub(crate) fn default_type_of(&self, def_id: DefId) -> rty::Ty {
        match rustc::lowering::lower_type_of(self.tcx, self.sess, def_id) {
            Ok(rustc_ty) => self.refine_ty_true(&rustc_ty),
            Err(_) => FatalError.raise(),
        }
    }

    fn default_variant_def(
        &self,
        adt_def_id: DefId,
        variant_def: &rustc_middle::ty::VariantDef,
    ) -> rty::PolyVariant {
        if let Ok(variant_def) =
            rustc::lowering::lower_variant_def(self.tcx, self.sess, adt_def_id, variant_def)
        {
            let fields = variant_def
                .field_tys
                .iter()
                .map(|ty| self.refine_ty_true(ty))
                .collect_vec();
            let rustc::ty::TyKind::Adt(def_id, substs) = variant_def.ret.kind() else {
                panic!();
            };
            let substs = substs
                .iter()
                .map(|arg| {
                    self.refine_generic_arg(arg, &mut |sorts| Binders::new(rty::Pred::tt(), sorts))
                })
                .collect_vec();
            let bty = rty::BaseTy::adt(self.adt_def(*def_id), substs);
            let ret = rty::VariantRet { bty, indices: List::from_vec(vec![]) };
            Binders::new(rty::VariantDef::new(fields, ret), vec![])
        } else {
            FatalError.raise()
        }
    }

    pub fn refine_fn_sig(
        &self,
        fn_sig: &rustc::ty::FnSig,
        mk_pred: &mut impl FnMut(&[rty::Sort]) -> Binders<rty::Pred>,
    ) -> rty::PolySig {
        let args = fn_sig
            .inputs()
            .iter()
            .map(|ty| self.refine_ty(ty, mk_pred))
            .collect_vec();
        let ret = self.refine_ty(&fn_sig.output(), mk_pred);
        rty::PolySig::new(rty::FnSig::new(vec![], args, ret, vec![]), vec![])
    }

    pub fn refine_ty(
        &self,
        ty: &rustc::ty::Ty,
        mk_pred: &mut impl FnMut(&[rty::Sort]) -> Binders<rty::Pred>,
    ) -> rty::Ty {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Never => return rty::Ty::never(),
            rustc::ty::TyKind::Param(param_ty) => return rty::Ty::param(*param_ty),
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Mut) => {
                return rty::Ty::mk_ref(rty::RefKind::Mut, self.refine_ty(ty, mk_pred));
            }
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Not) => {
                return rty::Ty::mk_ref(rty::RefKind::Shr, self.refine_ty(ty, mk_pred));
            }
            rustc::ty::TyKind::Float(float_ty) => return rty::Ty::float(*float_ty),
            rustc::ty::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.refine_ty(ty, mk_pred))
                    .collect_vec();
                return rty::Ty::tuple(tys);
            }
            rustc::ty::TyKind::Adt(def_id, substs) => {
                let adt_def = self.adt_def(*def_id);
                let substs = substs
                    .iter()
                    .map(|arg| self.refine_generic_arg(arg, mk_pred))
                    .collect_vec();
                rty::BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Bool => rty::BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            rustc::ty::TyKind::Str => rty::BaseTy::Str,
            rustc::ty::TyKind::Array(ty, len) => {
                rty::BaseTy::Array(self.refine_ty(ty, mk_pred), len.clone())
            }
            rustc::ty::TyKind::Slice(ty) => rty::BaseTy::Slice(self.refine_ty(ty, mk_pred)),
            rustc::ty::TyKind::Char => rty::BaseTy::Char,
        };
        let sorts = bty.sorts();
        if sorts.is_empty() {
            rty::Ty::indexed(bty, rty::RefineArgs::empty())
        } else {
            let pred = mk_pred(sorts);
            rty::Ty::exists(bty, pred)
        }
    }

    pub fn refine_generic_arg(
        &self,
        ty: &rustc::ty::GenericArg,
        mk_pred: &mut impl FnMut(&[rty::Sort]) -> Binders<rty::Pred>,
    ) -> rty::GenericArg {
        match ty {
            rustc::ty::GenericArg::Ty(ty) => rty::GenericArg::Ty(self.refine_ty(ty, mk_pred)),
            rustc::ty::GenericArg::Lifetime(_) => rty::GenericArg::Lifetime,
        }
    }
}
