//! *Refining* is the process of generating a refined version of a rust type.
//!
//! Concretely, this module provides functions to go from types in [`rustc::ty`] to types in [`rty`].
use std::iter;

use flux_common::bug;
use itertools::Itertools;
use rustc_hir::def_id::DefId;

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

pub(crate) fn refine_variant_def(
    genv: &GlobalEnv,
    def_id: DefId,
    variant_def: &rustc::ty::VariantDef,
) -> rty::PolyVariant {
    let generics = genv.generics_of(def_id);
    let fields = variant_def
        .field_tys
        .iter()
        .map(|ty| refine_ty(genv, &generics, ty, rty::Expr::tt))
        .collect_vec();
    let rustc::ty::TyKind::Adt(def_id, substs) = variant_def.ret.kind() else {
        bug!();
    };
    let substs = iter::zip(&generics.params, substs)
        .map(|(param, arg)| refine_generic_arg(genv, &generics, param, arg, rty::Expr::tt))
        .collect_vec();
    let bty = rty::BaseTy::adt(genv.adt_def(*def_id), substs);
    let ret = rty::Ty::indexed(bty, rty::Index::unit());
    let value = rty::VariantDef::new(fields, ret);
    rty::Binder::new(value, rty::Sort::unit())
}

pub(crate) fn refine_fn_sig(
    genv: &GlobalEnv,
    generics: &rty::Generics,
    fn_sig: &rustc::ty::FnSig,
    mk_pred: fn() -> rty::Expr,
) -> rty::PolySig {
    let args = fn_sig
        .inputs()
        .iter()
        .map(|ty| refine_ty(genv, generics, ty, mk_pred))
        .collect_vec();
    let ret = refine_ty(genv, generics, &fn_sig.output(), mk_pred);
    let output = rty::Binder::new(rty::FnOutput::new(ret, vec![]), rty::Sort::unit());
    rty::PolySig::new([], rty::FnSig::new(vec![], args, output))
}

pub(crate) fn refine_ty(
    genv: &GlobalEnv,
    generics: &rty::Generics,
    ty: &rustc::ty::Ty,
    mk_pred: fn() -> rty::Expr,
) -> rty::Ty {
    let ty = refine_ty_inner(genv, generics, ty, mk_pred);
    if ty.sort().is_unit() {
        ty.skip_binders()
    } else {
        rty::Ty::exists(ty)
    }
}

pub(crate) fn refine_generic_arg(
    genv: &GlobalEnv,
    generics: &rty::Generics,
    param: &rty::GenericParamDef,
    arg: &rustc::ty::GenericArg,
    mk_pred: fn() -> rty::Expr,
) -> rty::GenericArg {
    match (&param.kind, arg) {
        (rty::GenericParamDefKind::Type { .. }, rustc::ty::GenericArg::Ty(ty)) => {
            rty::GenericArg::Ty(refine_ty(genv, generics, ty, mk_pred))
        }
        (rty::GenericParamDefKind::BaseTy, rustc::ty::GenericArg::Ty(ty)) => {
            rty::GenericArg::BaseTy(refine_ty_inner(genv, generics, ty, mk_pred))
        }
        (rty::GenericParamDefKind::Lifetime, rustc::ty::GenericArg::Lifetime(_)) => {
            rty::GenericArg::Lifetime
        }
        _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
    }
}

fn refine_ty_inner(
    genv: &GlobalEnv,
    generics: &rty::Generics,
    ty: &rustc::ty::Ty,
    mk_pred: fn() -> rty::Expr,
) -> rty::Binder<rty::Ty> {
    let bty = match ty.kind() {
        rustc::ty::TyKind::Closure(did, _substs) => rty::BaseTy::Closure(*did),
        rustc::ty::TyKind::Never => rty::BaseTy::Never,
        rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Mut) => {
            rty::BaseTy::Ref(rty::RefKind::Mut, refine_ty(genv, generics, ty, mk_pred))
        }
        rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Not) => {
            rty::BaseTy::Ref(rty::RefKind::Shr, refine_ty(genv, generics, ty, mk_pred))
        }
        rustc::ty::TyKind::Float(float_ty) => rty::BaseTy::Float(*float_ty),
        rustc::ty::TyKind::Tuple(tys) => {
            let tys = tys
                .iter()
                .map(|ty| refine_ty(genv, generics, ty, mk_pred))
                .collect();
            rty::BaseTy::Tuple(tys)
        }
        rustc::ty::TyKind::Array(ty, len) => {
            rty::BaseTy::Array(refine_ty(genv, generics, ty, mk_pred), len.clone())
        }
        rustc::ty::TyKind::Param(param_ty) => {
            match generics.param_at(param_ty.index as usize, genv).kind {
                rty::GenericParamDefKind::Type { .. } => {
                    return rty::Binder::new(rty::Ty::param(*param_ty), rty::Sort::unit());
                }
                rty::GenericParamDefKind::BaseTy => rty::BaseTy::Param(*param_ty),
                rty::GenericParamDefKind::Lifetime => bug!(),
            }
        }
        rustc::ty::TyKind::Adt(def_id, substs) => {
            let adt_def = genv.adt_def(*def_id);
            let substs = iter::zip(&genv.generics_of(*def_id).params, substs)
                .map(|(param, arg)| refine_generic_arg(genv, generics, param, arg, mk_pred))
                .collect_vec();
            rty::BaseTy::adt(adt_def, substs)
        }
        rustc::ty::TyKind::Bool => rty::BaseTy::Bool,
        rustc::ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
        rustc::ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
        rustc::ty::TyKind::Str => rty::BaseTy::Str,
        rustc::ty::TyKind::Slice(ty) => rty::BaseTy::Slice(refine_ty(genv, generics, ty, mk_pred)),
        rustc::ty::TyKind::Char => rty::BaseTy::Char,
        rustc::ty::TyKind::FnSig(_) => todo!("refine_ty: FnSig"),
        rustc::ty::TyKind::RawPtr(ty, mu) => {
            rty::BaseTy::RawPtr(refine_ty(genv, generics, ty, rty::Expr::tt), *mu)
        }
    };
    let pred = mk_pred();
    let sort = bty.sort();
    let idx = rty::Expr::nu().eta_expand_tuple(&sort);
    let ty = if pred.is_trivially_true() {
        rty::Ty::indexed(bty, idx)
    } else {
        rty::Ty::constr(pred, rty::Ty::indexed(bty, idx))
    };
    rty::Binder::new(ty, sort)
}
