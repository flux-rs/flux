//! *Refining* is the process of generating a refined version of a rust type.
//!
//! Concretely, this module provides functions to go from types in [`flux_rustc_bridge::ty`] to
//! types in [`rty`].

use flux_arc_interner::{List, SliceInternable};
use flux_common::bug;
use flux_rustc_bridge::{ty, ty::GenericArgsExt as _};
use itertools::Itertools;
use rustc_abi::VariantIdx;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::ParamTy;

use super::{RefineArgsExt, fold::TypeFoldable};
use crate::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{self, Expr},
};

pub fn refine_generics(genv: GlobalEnv, def_id: DefId, generics: &ty::Generics) -> rty::Generics {
    let is_box = if let DefKind::Struct = genv.def_kind(def_id) {
        genv.tcx().adt_def(def_id).is_box()
    } else {
        false
    };
    let params = generics
        .params
        .iter()
        .map(|param| {
            rty::GenericParamDef {
                kind: refine_generic_param_def_kind(is_box, param.kind),
                index: param.index,
                name: param.name,
                def_id: param.def_id,
            }
        })
        .collect();

    rty::Generics {
        own_params: params,
        parent: generics.parent(),
        parent_count: generics.parent_count(),
        has_self: generics.orig.has_self,
    }
}

pub fn refine_generic_param_def_kind(
    is_box: bool,
    kind: ty::GenericParamDefKind,
) -> rty::GenericParamDefKind {
    match kind {
        ty::GenericParamDefKind::Lifetime => rty::GenericParamDefKind::Lifetime,
        ty::GenericParamDefKind::Type { has_default } => {
            if is_box {
                rty::GenericParamDefKind::Type { has_default }
            } else {
                rty::GenericParamDefKind::Base { has_default }
            }
        }
        ty::GenericParamDefKind::Const { has_default, .. } => {
            rty::GenericParamDefKind::Const { has_default }
        }
    }
}

pub struct Refiner<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: DefId,
    generics: rty::Generics,
    refine: fn(rty::BaseTy) -> rty::SubsetTyCtor,
}

impl<'genv, 'tcx> Refiner<'genv, 'tcx> {
    pub fn new_for_item(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: DefId,
        refine: fn(rty::BaseTy) -> rty::SubsetTyCtor,
    ) -> QueryResult<Self> {
        let generics = genv.generics_of(def_id)?;
        Ok(Self { genv, def_id, generics, refine })
    }

    pub fn default_for_item(genv: GlobalEnv<'genv, 'tcx>, def_id: DefId) -> QueryResult<Self> {
        Self::new_for_item(genv, def_id, refine_default)
    }

    pub fn with_holes(genv: GlobalEnv<'genv, 'tcx>, def_id: DefId) -> QueryResult<Self> {
        Self::new_for_item(genv, def_id, |bty| {
            let sort = bty.sort();
            let constr = rty::SubsetTy::new(
                bty.shift_in_escaping(1),
                rty::Expr::nu(),
                rty::Expr::hole(rty::HoleKind::Pred),
            );
            rty::Binder::bind_with_sort(constr, sort)
        })
    }

    pub fn refine<T: Refine + ?Sized>(&self, t: &T) -> QueryResult<T::Output> {
        t.refine(self)
    }

    fn refine_existential_predicate_generic_args(
        &self,
        def_id: DefId,
        args: &ty::GenericArgs,
    ) -> QueryResult<rty::GenericArgs> {
        let generics = self.generics_of(def_id)?;
        args.iter()
            .enumerate()
            .map(|(idx, arg)| {
                // We need to skip the generic for Self
                let param = generics.param_at(idx + 1, self.genv)?;
                self.refine_generic_arg(&param, arg)
            })
            .try_collect()
    }

    pub fn refine_variant_def(
        &self,
        adt_def_id: DefId,
        variant_idx: VariantIdx,
    ) -> QueryResult<rty::PolyVariant> {
        let adt_def = self.adt_def(adt_def_id)?;
        let variant_def = adt_def.variant(variant_idx);
        let fields = variant_def
            .fields
            .iter()
            .map(|fld| {
                let ty = self.genv.lower_type_of(fld.did)?.instantiate_identity();
                ty.refine(self)
            })
            .try_collect()?;

        let idx = if adt_def.sort_def().is_struct() {
            rty::Expr::unit_struct(adt_def_id)
        } else {
            rty::Expr::ctor_enum(adt_def_id, variant_idx)
        };
        let value = rty::VariantSig::new(
            adt_def,
            rty::GenericArg::identity_for_item(self.genv, adt_def_id)?,
            fields,
            idx,
            List::empty(),
        );

        Ok(rty::Binder::bind_with_vars(value, List::empty()))
    }

    pub fn refine_generic_args(
        &self,
        def_id: DefId,
        args: &ty::GenericArgs,
    ) -> QueryResult<rty::GenericArgs> {
        let generics = self.generics_of(def_id)?;
        args.iter()
            .enumerate()
            .map(|(idx, arg)| {
                let param = generics.param_at(idx, self.genv)?;
                self.refine_generic_arg(&param, arg)
            })
            .collect()
    }

    pub fn refine_generic_arg(
        &self,
        param: &rty::GenericParamDef,
        arg: &ty::GenericArg,
    ) -> QueryResult<rty::GenericArg> {
        match (&param.kind, arg) {
            (rty::GenericParamDefKind::Type { .. }, ty::GenericArg::Ty(ty)) => {
                Ok(rty::GenericArg::Ty(ty.refine(self)?))
            }
            (rty::GenericParamDefKind::Base { .. }, ty::GenericArg::Ty(ty)) => {
                let rty::TyOrBase::Base(contr) = self.refine_ty_or_base(ty)? else {
                    return Err(QueryErr::InvalidGenericArg { def_id: param.def_id });
                };
                Ok(rty::GenericArg::Base(contr))
            }
            (rty::GenericParamDefKind::Lifetime, ty::GenericArg::Lifetime(re)) => {
                Ok(rty::GenericArg::Lifetime(*re))
            }
            (rty::GenericParamDefKind::Const { .. }, ty::GenericArg::Const(ct)) => {
                Ok(rty::GenericArg::Const(ct.clone()))
            }
            _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
        }
    }

    fn refine_alias_ty(
        &self,
        alias_kind: ty::AliasKind,
        alias_ty: &ty::AliasTy,
    ) -> QueryResult<rty::AliasTy> {
        let def_id = alias_ty.def_id;
        let args = self.refine_generic_args(def_id, &alias_ty.args)?;

        let refine_args = if let ty::AliasKind::Opaque = alias_kind {
            rty::RefineArgs::for_item(self.genv, def_id, |param, _| {
                let param = param.instantiate(self.genv.tcx(), &args, &[]);
                Ok(rty::Expr::hole(rty::HoleKind::Expr(param.sort)))
            })?
        } else {
            List::empty()
        };

        Ok(rty::AliasTy::new(def_id, args, refine_args))
    }

    pub fn refine_ty_or_base(&self, ty: &ty::Ty) -> QueryResult<rty::TyOrBase> {
        let bty = match ty.kind() {
            ty::TyKind::Closure(did, args) => {
                let no_panic = self.genv.no_panic(did);
                let closure_args = args.as_closure();
                let upvar_tys = closure_args
                    .upvar_tys()
                    .iter()
                    .map(|ty| ty.refine(self))
                    .try_collect()?;
                rty::BaseTy::Closure(*did, upvar_tys, args.clone(), no_panic)
            }
            ty::TyKind::Coroutine(did, args) => {
                let coroutine_args = args.as_coroutine();
                let resume_ty = coroutine_args.resume_ty().refine(self)?;
                let upvar_tys = coroutine_args
                    .upvar_tys()
                    .map(|ty| ty.refine(self))
                    .try_collect()?;
                rty::BaseTy::Coroutine(*did, resume_ty, upvar_tys, args.clone())
            }
            ty::TyKind::CoroutineWitness(..) => {
                bug!("implement when we know what this is");
            }
            ty::TyKind::Never => rty::BaseTy::Never,
            ty::TyKind::Ref(r, ty, mutbl) => rty::BaseTy::Ref(*r, ty.refine(self)?, *mutbl),
            ty::TyKind::Float(float_ty) => rty::BaseTy::Float(*float_ty),
            ty::TyKind::Tuple(tys) => {
                let ctors = tys
                    .iter()
                    .map(|ty| ty.refine(self).map(|ty| ty_to_subset_ty_ctor(&ty)))
                    .try_collect()?;
                rty::BaseTy::Tuple(ctors)
            }
            ty::TyKind::Array(ty, len) => rty::BaseTy::Array(ty.refine(self)?, len.clone()),
            ty::TyKind::Param(param_ty) => {
                match self.param(*param_ty)?.kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return Ok(rty::TyOrBase::Ty(rty::Ty::param(*param_ty)));
                    }
                    rty::GenericParamDefKind::Base { .. } => rty::BaseTy::Param(*param_ty),
                    rty::GenericParamDefKind::Lifetime | rty::GenericParamDefKind::Const { .. } => {
                        bug!()
                    }
                }
            }
            ty::TyKind::Adt(adt_def, args) => {
                let adt_def = self.genv.adt_def(adt_def.did())?;
                let args = self.refine_generic_args(adt_def.did(), args)?;
                rty::BaseTy::adt(adt_def, args)
            }
            ty::TyKind::FnDef(def_id, args) => {
                let args = self.refine_generic_args(*def_id, args)?;
                rty::BaseTy::fn_def(*def_id, args)
            }
            ty::TyKind::Alias(kind, alias_ty) => {
                let alias_ty = self.as_default().refine_alias_ty(*kind, alias_ty)?;
                rty::BaseTy::Alias(*kind, alias_ty)
            }
            ty::TyKind::Bool => rty::BaseTy::Bool,
            ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            ty::TyKind::Foreign(def_id) => rty::BaseTy::Foreign(*def_id),
            ty::TyKind::Str => rty::BaseTy::Str,
            ty::TyKind::Slice(ty) => rty::BaseTy::Slice(ty.refine(self)?),
            ty::TyKind::Char => rty::BaseTy::Char,
            ty::TyKind::FnPtr(poly_fn_sig) => {
                rty::BaseTy::FnPtr(poly_fn_sig.refine(&self.as_default())?)
            }
            ty::TyKind::RawPtr(ty, mu) => rty::BaseTy::RawPtr(ty.refine(&self.as_default())?, *mu),
            ty::TyKind::Dynamic(exi_preds, r) => {
                let exi_preds = exi_preds
                    .iter()
                    .map(|pred| pred.refine(self))
                    .try_collect()?;
                rty::BaseTy::Dynamic(exi_preds, *r)
            }
            ty::TyKind::Pat => rty::BaseTy::Pat,
        };
        Ok(rty::TyOrBase::Base((self.refine)(bty)))
    }

    fn as_default(&self) -> Self {
        Refiner { refine: refine_default, generics: self.generics.clone(), ..*self }
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

pub trait Refine {
    type Output;

    fn refine(&self, refiner: &Refiner) -> QueryResult<Self::Output>;
}

impl Refine for ty::Ty {
    type Output = rty::Ty;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::Ty> {
        Ok(refiner.refine_ty_or_base(self)?.into_ty())
    }
}

impl<T: Refine> Refine for ty::Binder<T> {
    type Output = rty::Binder<T::Output>;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::Binder<T::Output>> {
        let vars = refine_bound_variables(self.vars());
        let inner = self.skip_binder_ref().refine(refiner)?;
        Ok(rty::Binder::bind_with_vars(inner, vars))
    }
}

impl Refine for ty::FnSig {
    type Output = rty::FnSig;

    // TODO(hof2)
    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::FnSig> {
        let inputs = self
            .inputs()
            .iter()
            .map(|ty| ty.refine(refiner))
            .try_collect()?;
        let ret = self.output().refine(refiner)?.shift_in_escaping(1);
        let output = rty::Binder::bind_with_vars(rty::FnOutput::new(ret, vec![]), List::empty());
        // TODO(hof2) make a hoister to hoist all the stuff out of the inputs,
        // the hoister will have a list of all the variables it hoisted and the
        // single hole for the "requires"; then we "fill" the hole with a KVAR
        // and generate a PolyFnSig with the hoisted variables
        // see `into_bb_env` in `type_env.rs` for an example.
        Ok(rty::FnSig::new(self.safety, self.abi, List::empty(), inputs, output, Expr::ff(), true))
    }
}

impl Refine for ty::Clause {
    type Output = rty::Clause;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::Clause> {
        Ok(rty::Clause { kind: self.kind.refine(refiner)? })
    }
}

impl Refine for ty::TraitRef {
    type Output = rty::TraitRef;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::TraitRef> {
        Ok(rty::TraitRef {
            def_id: self.def_id,
            args: refiner.refine_generic_args(self.def_id, &self.args)?,
        })
    }
}

impl Refine for ty::ClauseKind {
    type Output = rty::ClauseKind;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::ClauseKind> {
        let kind = match self {
            ty::ClauseKind::Trait(trait_pred) => {
                let pred = rty::TraitPredicate { trait_ref: trait_pred.trait_ref.refine(refiner)? };
                rty::ClauseKind::Trait(pred)
            }
            ty::ClauseKind::Projection(proj_pred) => {
                let rty::TyOrBase::Base(term) = refiner.refine_ty_or_base(&proj_pred.term)? else {
                    return Err(query_bug!(
                        refiner.def_id,
                        "sorry, we can't handle non-base associated types"
                    ));
                };
                let pred = rty::ProjectionPredicate {
                    projection_ty: refiner
                        .refine_alias_ty(ty::AliasKind::Projection, &proj_pred.projection_ty)?,
                    term,
                };
                rty::ClauseKind::Projection(pred)
            }
            ty::ClauseKind::RegionOutlives(pred) => {
                let pred = rty::OutlivesPredicate(pred.0, pred.1);
                rty::ClauseKind::RegionOutlives(pred)
            }
            ty::ClauseKind::TypeOutlives(pred) => {
                let pred = rty::OutlivesPredicate(pred.0.refine(refiner)?, pred.1);
                rty::ClauseKind::TypeOutlives(pred)
            }
            ty::ClauseKind::ConstArgHasType(const_, ty) => {
                rty::ClauseKind::ConstArgHasType(const_.clone(), ty.refine(&refiner.as_default())?)
            }
        };
        Ok(kind)
    }
}

impl Refine for ty::ExistentialPredicate {
    type Output = rty::ExistentialPredicate;

    fn refine(&self, refiner: &Refiner) -> QueryResult<Self::Output> {
        let pred = match self {
            ty::ExistentialPredicate::Trait(trait_ref) => {
                rty::ExistentialPredicate::Trait(rty::ExistentialTraitRef {
                    def_id: trait_ref.def_id,
                    args: refiner.refine_existential_predicate_generic_args(
                        trait_ref.def_id,
                        &trait_ref.args,
                    )?,
                })
            }
            ty::ExistentialPredicate::Projection(projection) => {
                let rty::TyOrBase::Base(term) = refiner.refine_ty_or_base(&projection.term)? else {
                    return Err(query_bug!(
                        refiner.def_id,
                        "sorry, we can't handle non-base associated types"
                    ));
                };
                rty::ExistentialPredicate::Projection(rty::ExistentialProjection {
                    def_id: projection.def_id,
                    args: refiner.refine_existential_predicate_generic_args(
                        projection.def_id,
                        &projection.args,
                    )?,
                    term,
                })
            }
            ty::ExistentialPredicate::AutoTrait(def_id) => {
                rty::ExistentialPredicate::AutoTrait(*def_id)
            }
        };
        Ok(pred)
    }
}

impl Refine for ty::GenericPredicates {
    type Output = rty::GenericPredicates;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::GenericPredicates> {
        Ok(rty::GenericPredicates {
            parent: self.parent,
            predicates: refiner.refine(&self.predicates)?,
        })
    }
}

impl<T> Refine for List<T>
where
    T: SliceInternable,
    T: Refine<Output: SliceInternable>,
{
    type Output = rty::List<T::Output>;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::List<T::Output>> {
        refiner.refine(&self[..])
    }
}

impl<T> Refine for [T]
where
    T: Refine<Output: SliceInternable>,
{
    type Output = rty::List<T::Output>;

    fn refine(&self, refiner: &Refiner) -> QueryResult<rty::List<T::Output>> {
        self.iter().map(|t| refiner.refine(t)).try_collect()
    }
}

fn refine_default(bty: rty::BaseTy) -> rty::SubsetTyCtor {
    let sort = bty.sort();
    let constr = rty::SubsetTy::trivial(bty.shift_in_escaping(1), rty::Expr::nu());
    rty::Binder::bind_with_sort(constr, sort)
}

fn ty_to_subset_ty_ctor(ty: &rty::Ty) -> rty::SubsetTyCtor {
    match ty.kind() {
        rty::TyKind::Indexed(bty, idx) => {
            let sort = bty.sort();
            rty::Binder::bind_with_sort(rty::SubsetTy::trivial(bty.clone(), idx.clone()), sort)
        }
        rty::TyKind::Constr(pred, inner_ty) => {
            if let rty::TyKind::Indexed(bty, idx) = inner_ty.kind() {
                let sort = bty.sort();
                rty::Binder::bind_with_sort(
                    rty::SubsetTy::new(bty.clone(), idx.clone(), pred.clone()),
                    sort,
                )
            } else {
                let bty = inner_ty
                    .as_bty_skipping_existentials()
                    .expect("expected base type")
                    .clone();
                let sort = bty.sort();
                rty::Binder::bind_with_sort(
                    rty::SubsetTy::new(bty, rty::Expr::nu(), pred.clone()),
                    sort,
                )
            }
        }
        _ => {
            let bty = ty
                .as_bty_skipping_existentials()
                .expect("expected base type")
                .clone();
            let sort = bty.sort();
            rty::Binder::bind_with_sort(rty::SubsetTy::trivial(bty, rty::Expr::nu()), sort)
        }
    }
}

pub fn refine_bound_variables(vars: &[ty::BoundVariableKind]) -> List<rty::BoundVariableKind> {
    vars.iter()
        .map(|kind| {
            match kind {
                ty::BoundVariableKind::Region(kind) => rty::BoundVariableKind::Region(*kind),
            }
        })
        .collect()
}
