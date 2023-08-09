//! *Refining* is the process of generating a refined version of a rust type.
//!
//! Concretely, this module provides functions to go from types in [`rustc::ty`] to types in [`rty`].
use std::iter;

use flux_common::{bug, iter::IterExt};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::ParamTy;

use super::fold::TypeFoldable;
use crate::{
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty,
    rustc::{self, ty::Substs},
};

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

pub(crate) struct Refiner<'a, 'tcx> {
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

    pub(crate) fn default(genv: &'a GlobalEnv<'a, 'tcx>, generics: &'a rty::Generics) -> Self {
        Self { genv, generics, refine: refine_default }
    }

    pub(crate) fn with_holes(genv: &'a GlobalEnv<'a, 'tcx>, generics: &'a rty::Generics) -> Self {
        Self {
            genv,
            generics,
            refine: |bty| {
                let sort = bty.sort();
                let indexed = rty::Ty::indexed(bty.shift_in_escaping(1), rty::Expr::nu());
                let constr = rty::Ty::constr(rty::Expr::hole(), indexed);
                rty::Binder::with_sort(constr, sort)
            },
        }
    }

    pub(crate) fn refine_generic_predicates(
        &self,
        generics: &rustc::ty::GenericPredicates,
    ) -> QueryResult<rty::GenericPredicates> {
        let predicates = generics
            .predicates
            .iter()
            .map(|pred| -> QueryResult<rty::Clause> {
                let vars = refine_bound_variables(pred.kind.vars());
                let kind = match pred.kind.as_ref().skip_binder() {
                    rustc::ty::ClauseKind::FnTrait { bounded_ty, tupled_args, output, kind } => {
                        let pred = rty::FnTraitPredicate {
                            self_ty: self.refine_ty(bounded_ty)?,
                            tupled_args: self.refine_ty(tupled_args)?,
                            output: self.refine_ty(output)?,
                            kind: *kind,
                        };
                        rty::Binder::new(rty::ClauseKind::FnTrait(pred), vars)
                    }
                    rustc::ty::ClauseKind::Projection(proj_pred) => {
                        let proj_pred = rty::ProjectionPredicate {
                            alias_ty: self.refine_alias_ty(&proj_pred.projection_ty)?,
                            term: self.as_default().refine_ty(&proj_pred.term)?,
                        };
                        rty::Binder::new(rty::ClauseKind::Projection(proj_pred), vars)
                    }
                };
                Ok(rty::Clause { kind })
            })
            .try_collect()?;

        Ok(rty::GenericPredicates { parent: generics.parent, predicates })
    }

    pub(crate) fn refine_variant_def(
        &self,
        fields: &[rustc::ty::Ty],
        ret: &rustc::ty::Ty,
    ) -> QueryResult<rty::PolyVariant> {
        let fields = fields.iter().map(|ty| self.refine_ty(ty)).try_collect()?;
        let rustc::ty::TyKind::Adt(adt_def, substs) = ret.kind() else {
            bug!();
        };
        let substs = iter::zip(&self.generics.params, substs)
            .map(|(param, arg)| self.refine_generic_arg(param, arg))
            .try_collect_vec()?;
        let bty = rty::BaseTy::adt(self.adt_def(adt_def.did())?, substs);
        let ret = rty::Ty::indexed(bty, rty::Expr::unit());
        let value = rty::VariantSig::new(fields, ret);
        Ok(rty::Binder::new(value, List::empty()))
    }

    pub(crate) fn refine_binders<S, T, F>(
        &self,
        thing: &rustc::ty::Binder<S>,
        mut f: F,
    ) -> QueryResult<rty::Binder<T>>
    where
        F: FnMut(&S) -> QueryResult<T>,
    {
        let vars = refine_bound_variables(thing.vars());
        let inner = thing.as_ref().skip_binder();
        let inner = f(inner)?;
        Ok(rty::Binder::new(inner, vars))
    }

    pub(crate) fn refine_poly_fn_sig(
        &self,
        fn_sig: &rustc::ty::PolyFnSig,
    ) -> QueryResult<rty::PolyFnSig> {
        self.refine_binders(fn_sig, |fn_sig| {
            let args = fn_sig
                .inputs()
                .iter()
                .map(|ty| self.refine_ty(ty))
                .try_collect_vec()?;
            let ret = self.refine_ty(fn_sig.output())?.shift_in_escaping(1);
            let output = rty::Binder::new(rty::FnOutput::new(ret, vec![]), List::empty());
            Ok(rty::FnSig::new(vec![], args, output))
        })
        // let vars = refine_bound_variables(fn_sig.vars());
        // let fn_sig = fn_sig.as_ref().skip_binder();
        // let args = fn_sig
        //     .inputs()
        //     .iter()
        //     .map(|ty| self.refine_ty(ty))
        //     .try_collect_vec()?;
        // let ret = self.refine_ty(fn_sig.output())?.shift_in_escaping(1);
        // let output = rty::Binder::new(rty::FnOutput::new(ret, vec![]), List::empty());
        // Ok(rty::PolyFnSig::new(rty::FnSig::new(vec![], args, output), vars))
    }

    pub(crate) fn refine_generic_arg(
        &self,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        match (&param.kind, arg) {
            (rty::GenericParamDefKind::Type { .. }, rustc::ty::GenericArg::Ty(ty)) => {
                Ok(rty::GenericArg::Ty(self.refine_ty(ty)?))
            }
            (rty::GenericParamDefKind::BaseTy, rustc::ty::GenericArg::Ty(ty)) => {
                Ok(rty::GenericArg::BaseTy(self.refine_poly_ty(ty)?))
            }
            (rty::GenericParamDefKind::Lifetime, rustc::ty::GenericArg::Lifetime(re)) => {
                Ok(rty::GenericArg::Lifetime(*re))
            }
            _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
        }
    }

    pub(crate) fn refine_alias_ty(
        &self,
        alias_ty: &rustc::ty::AliasTy,
    ) -> QueryResult<rty::AliasTy> {
        let def_id = alias_ty.def_id;
        let generics = self.generics_of(def_id)?;
        let args = iter::zip(&generics.params, alias_ty.substs.iter())
            .map(|(param, arg)| self.as_default().refine_generic_arg(param, arg))
            .try_collect_vec()?;
        Ok(rty::AliasTy::new(def_id, args))
    }

    pub(crate) fn refine_ty(&self, ty: &rustc::ty::Ty) -> QueryResult<rty::Ty> {
        let ty = self.refine_poly_ty(ty)?;
        match &ty.vars()[..] {
            [] => Ok(ty.skip_binder().shift_out_escaping(1)),
            [rty::BoundVariableKind::Refine(s, _)] if s.is_unit() => {
                Ok(ty.replace_bound_exprs(&[rty::Expr::unit()]))
            }
            _ => Ok(rty::Ty::exists(ty)),
        }
    }
    fn refine_alias_kind(kind: &rustc::ty::AliasKind) -> rty::AliasKind {
        match kind {
            rustc::ty::AliasKind::Projection => rty::AliasKind::Projection,
            rustc::ty::AliasKind::Opaque => rty::AliasKind::Opaque,
        }
    }

    fn refine_generic_args(&self, args: &Substs) -> QueryResult<List<rty::Ty>> {
        if let rustc::ty::GenericArg::Ty(ty) = &args[args.len() - 1] &&
           let rustc::ty::TyKind::Tuple(tys) = ty.kind()
        {
          tys.iter().map(|ty| self.refine_ty(ty)).try_collect()
        } else {
            bug!()
        }
    }

    fn refine_poly_ty(&self, ty: &rustc::ty::Ty) -> QueryResult<rty::PolyTy> {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Closure(did, args) => {
                rty::BaseTy::Closure(*did, self.refine_generic_args(args)?)
            }
            rustc::ty::TyKind::Generator(did, args) => {
                rty::BaseTy::Generator(*did, self.refine_generic_args(args)?)
            }
            rustc::ty::TyKind::Never => rty::BaseTy::Never,
            rustc::ty::TyKind::Ref(r, ty, mutbl) => {
                rty::BaseTy::Ref(*r, self.refine_ty(ty)?, *mutbl)
            }
            rustc::ty::TyKind::Float(float_ty) => rty::BaseTy::Float(*float_ty),
            rustc::ty::TyKind::Tuple(tys) => {
                let tys = tys.iter().map(|ty| self.refine_ty(ty)).try_collect()?;
                rty::BaseTy::Tuple(tys)
            }
            rustc::ty::TyKind::Array(ty, len) => {
                rty::BaseTy::Array(self.refine_ty(ty)?, len.clone())
            }
            rustc::ty::TyKind::Param(param_ty) => {
                match self.param(*param_ty)?.kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return Ok(rty::Binder::new(rty::Ty::param(*param_ty), List::empty()));
                    }
                    rty::GenericParamDefKind::BaseTy => rty::BaseTy::Param(*param_ty),
                    rty::GenericParamDefKind::Lifetime => bug!(),
                }
            }
            rustc::ty::TyKind::Adt(adt_def, substs) => {
                let adt_def = self.genv.adt_def(adt_def.did())?;
                let substs = iter::zip(&self.generics_of(adt_def.did())?.params, substs)
                    .map(|(param, arg)| self.refine_generic_arg(param, arg))
                    .try_collect_vec()?;
                rty::BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Alias(kind, alias_ty) => {
                let kind = Self::refine_alias_kind(kind);
                let alias_ty = self.refine_alias_ty(alias_ty)?;
                rty::BaseTy::alias(kind, alias_ty)
            }

            rustc::ty::TyKind::Bool => rty::BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            rustc::ty::TyKind::Str => rty::BaseTy::Str,
            rustc::ty::TyKind::Slice(ty) => rty::BaseTy::Slice(self.refine_ty(ty)?),
            rustc::ty::TyKind::Char => rty::BaseTy::Char,
            rustc::ty::TyKind::FnPtr(_) => todo!("refine_ty: FnSig"),
            rustc::ty::TyKind::RawPtr(ty, mu) => {
                rty::BaseTy::RawPtr(self.as_default().refine_ty(ty)?, *mu)
            }
            rustc::ty::TyKind::GeneratorWitness(args) => {
                let args = self.refine_binders(args, |tys| {
                    Ok(List::from_vec(tys.iter().map(|ty| self.refine_ty(ty)).try_collect_vec()?))
                })?;
                rty::BaseTy::GeneratorWitness(args)
            }
        };
        Ok((self.refine)(bty))
    }

    fn as_default(&self) -> Self {
        Refiner { refine: refine_default, ..*self }
    }

    fn adt_def(&self, def_id: DefId) -> QueryResult<rty::AdtDef> {
        self.genv.adt_def(def_id)
    }

    fn generics_of(&self, def_id: DefId) -> QueryResult<rty::Generics> {
        self.genv.generics_of(def_id)
    }

    fn param(&self, param_ty: ParamTy) -> QueryResult<rty::GenericParamDef> {
        self.generics.param_at(param_ty.index as usize, self.genv)
    }
}

pub fn refine_default(bty: rty::BaseTy) -> rty::Binder<rty::Ty> {
    let sort = bty.sort();
    rty::Binder::with_sort(rty::Ty::indexed(bty.shift_in_escaping(1), rty::Expr::nu()), sort)
}

pub fn refine_bound_variables(
    vars: &[rustc::ty::BoundVariableKind],
) -> List<rty::BoundVariableKind> {
    vars.iter()
        .map(|kind| {
            match kind {
                rustc::ty::BoundVariableKind::Region(kind) => rty::BoundVariableKind::Region(*kind),
            }
        })
        .collect()
}
