//! *Refining* is the process of generating a refined version of a rust type.
//!
//! Concretely, this module provides functions to go from types in [`rustc::ty`] to types in [`rty`].
use std::iter;

use flux_common::bug;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::ParamTy;

use crate::{global_env::GlobalEnv, rty, rustc};

pub(crate) fn refine_generics(generics: &rustc::ty::Generics) -> rty::Generics {
    let params = generics
        .params
        .iter()
        .map(|param| {
            let kind = match param.kind {
                rustc::ty::GenericParamDefKind::Lifetime => rty::GenericParamDefKind::Lifetime,
                rustc::ty::GenericParamDefKind::Type { has_default } => {
                    rty::GenericParamDefKind::Type { has_default }
                }
            };
            rty::GenericParamDef {
                kind,
                index: param.index,
                name: param.name,
                def_id: param.def_id,
            }
        })
        .collect();
    rty::Generics { params, parent_count: generics.orig.parent_count, parent: generics.orig.parent }
}

pub struct Refiner<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    generics: &'a rty::Generics,
    refine: fn(rty::BaseTy) -> rty::Binder<rty::Ty>,
}

impl<'a, 'tcx> Refiner<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        generics: &'a rty::Generics,
        refine: fn(rty::BaseTy) -> rty::Binder<rty::Ty>,
    ) -> Self {
        Self { genv, generics, refine }
    }

    pub fn default(genv: &'a GlobalEnv<'a, 'tcx>, generics: &'a rty::Generics) -> Self {
        Self { genv, generics, refine: refine_default }
    }

    pub(crate) fn with_holes(genv: &'a GlobalEnv<'a, 'tcx>, generics: &'a rty::Generics) -> Self {
        Self {
            genv,
            generics,
            refine: |bty| {
                let sort = bty.sort();
                let indexed = rty::Ty::indexed(bty, rty::Expr::nu());
                let constr = rty::Ty::constr(rty::Expr::hole(), indexed);
                rty::Binder::new(constr, sort)
            },
        }
    }

    pub(crate) fn refine_generic_predicates(
        &self,
        generics: &rustc::ty::GenericPredicates,
    ) -> rty::GenericPredicates {
        let predicates = generics
            .predicates
            .iter()
            .map(|pred| {
                match pred.kind.as_ref().skip_binder() {
                    rustc::ty::PredicateKind::FnTrait { bounded_ty, tupled_args, output, kind } => {
                        let pred = rty::FnTraitPredicate {
                            bounded_ty: self.refine_ty(bounded_ty),
                            tupled_args: self.refine_ty(tupled_args),
                            output: self.refine_ty(output),
                            kind: *kind,
                        };
                        rty::Predicate::FnTrait(pred)
                    }
                }
            })
            .collect();

        rty::GenericPredicates { parent: generics.parent, predicates }
    }

    pub(crate) fn refine_variant_def(
        &self,
        variant_def: &rustc::ty::VariantDef,
    ) -> rty::PolyVariant {
        let fields = variant_def
            .field_tys
            .iter()
            .map(|ty| self.refine_ty(ty))
            .collect_vec();
        let rustc::ty::TyKind::Adt(def_id, substs) = variant_def.ret.kind() else {
            bug!();
        };
        let substs = iter::zip(&self.generics.params, substs)
            .map(|(param, arg)| self.refine_generic_arg(param, arg))
            .collect_vec();
        let bty = rty::BaseTy::adt(self.adt_def(*def_id), substs);
        let ret = rty::Ty::indexed(bty, rty::Index::unit());
        let value = rty::VariantDef::new(fields, ret);
        rty::Binder::new(value, rty::Sort::unit())
    }

    pub fn refine_fn_sig(&self, fn_sig: &rustc::ty::FnSig) -> rty::PolySig {
        let args = fn_sig
            .inputs()
            .iter()
            .map(|ty| self.refine_ty(ty))
            .collect_vec();
        let ret = self.refine_ty(&fn_sig.output());
        let output = rty::Binder::new(rty::FnOutput::new(ret, vec![]), rty::Sort::unit());
        rty::PolySig::new([], rty::FnSig::new(vec![], args, output))
    }

    pub(crate) fn refine_generic_arg(
        &self,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> rty::GenericArg {
        match (&param.kind, arg) {
            (rty::GenericParamDefKind::Type { .. }, rustc::ty::GenericArg::Ty(ty)) => {
                rty::GenericArg::Ty(self.refine_ty(ty))
            }
            (rty::GenericParamDefKind::BaseTy, rustc::ty::GenericArg::Ty(ty)) => {
                rty::GenericArg::BaseTy(self.refine_bound_ty(ty))
            }
            (rty::GenericParamDefKind::Lifetime, rustc::ty::GenericArg::Lifetime(_)) => {
                rty::GenericArg::Lifetime
            }
            _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
        }
    }

    pub(crate) fn refine_ty(&self, ty: &rustc::ty::Ty) -> rty::Ty {
        let ty = self.refine_bound_ty(ty);
        if ty.sort().is_unit() {
            ty.replace_bvar(&rty::Expr::unit())
        } else {
            rty::Ty::exists(ty)
        }
    }

    fn refine_bound_ty(&self, ty: &rustc::ty::Ty) -> rty::Binder<rty::Ty> {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Closure(did, _substs) => rty::BaseTy::Closure(*did),
            rustc::ty::TyKind::Never => rty::BaseTy::Never,
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Mut) => {
                rty::BaseTy::Ref(rty::RefKind::Mut, self.refine_ty(ty))
            }
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Not) => {
                rty::BaseTy::Ref(rty::RefKind::Shr, self.refine_ty(ty))
            }
            rustc::ty::TyKind::Float(float_ty) => rty::BaseTy::Float(*float_ty),
            rustc::ty::TyKind::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.refine_ty(ty)).collect();
                rty::BaseTy::Tuple(tys)
            }
            rustc::ty::TyKind::Array(ty, len) => {
                rty::BaseTy::Array(self.refine_ty(ty), len.clone())
            }
            rustc::ty::TyKind::Param(param_ty) => {
                match self.param(*param_ty).kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return rty::Binder::new(rty::Ty::param(*param_ty), rty::Sort::unit());
                    }
                    rty::GenericParamDefKind::BaseTy => rty::BaseTy::Param(*param_ty),
                    rty::GenericParamDefKind::Lifetime => bug!(),
                }
            }
            rustc::ty::TyKind::Adt(def_id, substs) => {
                let adt_def = self.genv.adt_def(*def_id);
                let substs = iter::zip(&self.generics_of(*def_id).params, substs)
                    .map(|(param, arg)| self.refine_generic_arg(param, arg))
                    .collect_vec();
                rty::BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Bool => rty::BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            rustc::ty::TyKind::Str => rty::BaseTy::Str,
            rustc::ty::TyKind::Slice(ty) => rty::BaseTy::Slice(self.refine_ty(ty)),
            rustc::ty::TyKind::Char => rty::BaseTy::Char,
            rustc::ty::TyKind::FnSig(_) => todo!("refine_ty: FnSig"),
            rustc::ty::TyKind::RawPtr(ty, mu) => {
                rty::BaseTy::RawPtr(self.as_default().refine_ty(ty), *mu)
            }
        };
        (self.refine)(bty)
    }

    fn as_default(&self) -> Self {
        Refiner { refine: refine_default, ..*self }
    }

    fn adt_def(&self, def_id: DefId) -> rty::AdtDef {
        self.genv.adt_def(def_id)
    }

    fn generics_of(&self, def_id: DefId) -> rty::Generics {
        self.genv.generics_of(def_id)
    }

    fn param(&self, param_ty: ParamTy) -> rty::GenericParamDef {
        self.generics.param_at(param_ty.index as usize, self.genv)
    }
}

fn refine_default(bty: rty::BaseTy) -> rty::Binder<rty::Ty> {
    let sort = bty.sort();
    rty::Binder::new(rty::Ty::indexed(bty, rty::Expr::nu()), sort)
}
