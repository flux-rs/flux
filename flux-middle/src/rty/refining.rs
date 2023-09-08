//! *Refining* is the process of generating a refined version of a rust type.
//!
//! Concretely, this module provides functions to go from types in [`rustc::ty`] to types in [`rty`].
use std::iter;

use flux_common::{bug, iter::IterExt};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ClosureKind, ParamTy};

use super::{fold::TypeFoldable, OpaqueRefineArgs};
use crate::{global_env::GlobalEnv, intern::List, queries::QueryResult, rty, rustc};

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
                rustc::ty::GenericParamDefKind::Const { has_default } => {
                    rty::GenericParamDefKind::Const { has_default }
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
    rty::Generics {
        params,
        refine_params: vec![],
        parent_count: generics.orig.parent_count,
        parent: generics.orig.parent,
    }
}

pub struct Refiner<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    generics: &'a rty::Generics,
    // see [NOTE:Opaque-Refine-Args]
    opaque_refine_args: Option<&'a OpaqueRefineArgs>,
    refine: fn(rty::BaseTy) -> rty::Binder<rty::Ty>,
}

impl<'a, 'tcx> Refiner<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        generics: &'a rty::Generics,
        opaque_refine_args: &'a OpaqueRefineArgs,
        refine: fn(rty::BaseTy) -> rty::Binder<rty::Ty>,
    ) -> Self {
        Self { genv, generics, opaque_refine_args: Some(opaque_refine_args), refine }
    }

    pub fn default(genv: &'a GlobalEnv<'a, 'tcx>, generics: &'a rty::Generics) -> Self {
        Self { genv, generics, opaque_refine_args: None, refine: refine_default }
    }

    pub(crate) fn with_holes(
        genv: &'a GlobalEnv<'a, 'tcx>,
        generics: &'a rty::Generics,
        opaque_refine_args: Option<&'a OpaqueRefineArgs>,
    ) -> Self {
        Self {
            genv,
            generics,
            opaque_refine_args,
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
        Ok(rty::GenericPredicates {
            parent: generics.parent,
            predicates: self.refine_clauses(&generics.predicates)?,
        })
    }

    pub(crate) fn refine_clauses(
        &self,
        clauses: &[rustc::ty::Clause],
    ) -> QueryResult<List<rty::Clause>> {
        let clauses = clauses
            .iter()
            .flat_map(|clause| self.refine_clause(clauses, clause).transpose())
            .try_collect()?;

        Ok(clauses)
    }

    fn refine_clause(
        &self,
        clauses: &[rustc::ty::Clause],
        clause: &rustc::ty::Clause,
    ) -> QueryResult<Option<rty::Clause>> {
        let kind = match &clause.kind {
            rustc::ty::ClauseKind::Trait(trait_pred) => {
                let trait_ref = &trait_pred.trait_ref;
                if let Some(kind) = self.genv.tcx.fn_trait_kind_from_def_id(trait_ref.def_id) {
                    self.refine_fn_trait_pred(clauses, kind, trait_ref)?
                } else {
                    let pred = rty::TraitPredicate { trait_ref: self.refine_trait_ref(trait_ref)? };
                    rty::ClauseKind::Trait(pred)
                }
            }
            rustc::ty::ClauseKind::Projection(proj_pred) => {
                if self.genv.is_fn_once_output(proj_pred.projection_ty.def_id) {
                    return Ok(None);
                }
                let pred = rty::ProjectionPredicate {
                    projection_ty: self.refine_alias_ty(
                        &rustc::ty::AliasKind::Projection,
                        &proj_pred.projection_ty,
                    )?,
                    term: self.as_default().refine_ty(&proj_pred.term)?,
                };
                rty::ClauseKind::Projection(pred)
            }
        };
        Ok(Some(rty::Clause { kind }))
    }

    fn refine_fn_trait_pred(
        &self,
        clauses: &[rustc::ty::Clause],
        kind: ClosureKind,
        trait_ref: &rustc::ty::TraitRef,
    ) -> QueryResult<rty::ClauseKind> {
        let mut candidates = vec![];
        for clause in clauses {
            if let rustc::ty::ClauseKind::Projection(trait_pred) = &clause.kind
                && self.genv.is_fn_once_output(trait_pred.projection_ty.def_id)
                && trait_pred.projection_ty.self_ty() == trait_ref.self_ty()
            {
                candidates.push(trait_pred);
            }
        }
        assert!(candidates.len() == 1);
        let pred = candidates.first().unwrap();

        let pred = rty::FnTraitPredicate {
            kind,
            self_ty: self.refine_ty(trait_ref.args[0].expect_type())?,
            tupled_args: self.refine_ty(trait_ref.args[1].expect_type())?,
            output: self.refine_ty(&pred.term)?,
        };
        Ok(rty::ClauseKind::FnTrait(pred))
    }

    fn refine_trait_ref(&self, trait_ref: &rustc::ty::TraitRef) -> QueryResult<rty::TraitRef> {
        let trait_ref = rty::TraitRef {
            def_id: trait_ref.def_id,
            args: trait_ref
                .args
                .iter()
                .map(|arg| self.refine_generic_arg_raw(arg))
                .try_collect()?,
        };
        Ok(trait_ref)
    }

    pub(crate) fn refine_variant_def(
        &self,
        fields: &[rustc::ty::Ty],
        ret: &rustc::ty::Ty,
    ) -> QueryResult<rty::PolyVariant> {
        let fields = fields.iter().map(|ty| self.refine_ty(ty)).try_collect()?;
        let rustc::ty::TyKind::Adt(adt_def, args) = ret.kind() else {
            bug!();
        };
        let args = iter::zip(&self.generics.params, args)
            .map(|(param, arg)| self.refine_generic_arg(param, arg))
            .try_collect_vec()?;
        let bty = rty::BaseTy::adt(self.adt_def(adt_def.did())?, args);
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
            (rty::GenericParamDefKind::Const { .. }, rustc::ty::GenericArg::Const(ct)) => {
                Ok(rty::GenericArg::Const(ct.clone()))
            }
            _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
        }
    }

    pub(crate) fn refine_generic_arg_raw(
        &self,
        arg: &rustc::ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        match arg {
            rustc::ty::GenericArg::Ty(ty) => Ok(rty::GenericArg::Ty(self.refine_ty(ty)?)),
            rustc::ty::GenericArg::Lifetime(re) => Ok(rty::GenericArg::Lifetime(*re)),
            rustc::ty::GenericArg::Const(c) => Ok(rty::GenericArg::Const(c.clone())),
        }
    }

    pub(crate) fn refine_alias_ty(
        &self,
        alias_kind: &rustc::ty::AliasKind,
        alias_ty: &rustc::ty::AliasTy,
    ) -> QueryResult<rty::AliasTy> {
        let def_id = alias_ty.def_id;
        let generics = self.generics_of(def_id)?;
        let args = iter::zip(&generics.params, alias_ty.args.iter())
            .map(|(param, arg)| self.as_default().refine_generic_arg(param, arg))
            .try_collect_vec()?;
        let refine_args = self.refine_args_of(def_id, alias_kind);
        let res = rty::AliasTy::new(def_id, args, refine_args);
        Ok(res)
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

    pub fn refine_poly_ty(&self, ty: &rustc::ty::Ty) -> QueryResult<rty::PolyTy> {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Closure(did, args) => {
                let args = args.as_closure();
                let upvar_tys = args
                    .upvar_tys()
                    .iter()
                    .map(|ty| self.refine_ty(ty))
                    .try_collect()?;
                rty::BaseTy::Closure(*did, upvar_tys)
            }
            rustc::ty::TyKind::Generator(did, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.refine_generic_arg_raw(arg))
                    .try_collect()?;
                rty::BaseTy::Generator(*did, args)
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
                    rty::GenericParamDefKind::Const { .. } => bug!(),
                }
            }
            rustc::ty::TyKind::Adt(adt_def, args) => {
                let adt_def = self.genv.adt_def(adt_def.did())?;
                let args = iter::zip(&self.generics_of(adt_def.did())?.params, args)
                    .map(|(param, arg)| self.refine_generic_arg(param, arg))
                    .try_collect_vec()?;
                rty::BaseTy::adt(adt_def, args)
            }
            rustc::ty::TyKind::Alias(alias_kind, alias_ty) => {
                let kind = Self::refine_alias_kind(alias_kind);
                let alias_ty = self.refine_alias_ty(alias_kind, alias_ty)?;
                return Ok(rty::Binder::new(rty::Ty::alias(kind, alias_ty), List::empty()));
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

    fn refine_args_of(&self, def_id: DefId, alias_kind: &rustc::ty::AliasKind) -> rty::RefineArgs {
        if let rustc::ty::AliasKind::Opaque = alias_kind &&
           let Some(opaque_refine_args) = self.opaque_refine_args {
            opaque_refine_args.get(&def_id).unwrap().clone()
        } else {
            List::empty()
        }
    }

    fn param(&self, param_ty: ParamTy) -> QueryResult<rty::GenericParamDef> {
        self.generics.param_at(param_ty.index as usize, self.genv)
    }
}

fn refine_default(bty: rty::BaseTy) -> rty::Binder<rty::Ty> {
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
