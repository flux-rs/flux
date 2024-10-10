use std::iter;

use flux_arc_interner::List;
use flux_common::{bug, tracked_span_bug};
use flux_rustc_bridge::{lowering::Lower, ToRustc};
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::InferCtxt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSource, ObligationCause},
    ty::TyCtxt,
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{FallibleTypeFolder, TypeFoldable, TypeSuperFoldable},
    subst::{GenericsSubstDelegate, GenericsSubstFolder},
    AliasKind, AliasReft, AliasTy, BaseTy, Clause, ClauseKind, Const, EarlyBinder, Expr, ExprKind,
    GenericArg, ProjectionPredicate, RefineArgs, Region, Sort, SubsetTy, SubsetTyCtor, Ty, TyCtor,
    TyKind,
};
use crate::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::{fold::TypeVisitable, refining::Refiner},
};

pub(crate) struct Normalizer<'genv, 'tcx, 'cx> {
    genv: GlobalEnv<'genv, 'tcx>,
    selcx: SelectionContext<'cx, 'tcx>,
    def_id: DefId,
    param_env: List<Clause>,
}

impl<'genv, 'tcx, 'cx> Normalizer<'genv, 'tcx, 'cx> {
    pub(crate) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        infcx: &'cx InferCtxt<'tcx>,
        callsite_def_id: DefId,
    ) -> QueryResult<Self> {
        let param_env = genv
            .predicates_of(callsite_def_id)?
            .instantiate_identity()
            .predicates
            .clone();
        let selcx = SelectionContext::new(infcx);
        Ok(Normalizer { genv, selcx, def_id: callsite_def_id, param_env })
    }

    fn get_impl_id_of_alias_reft(&mut self, alias_reft: &AliasReft) -> QueryResult<Option<DefId>> {
        let tcx = self.tcx();
        let def_id = self.def_id;
        let selcx = &mut self.selcx;

        let trait_pred = Obligation::new(
            tcx,
            ObligationCause::dummy(),
            tcx.param_env(def_id),
            alias_reft.to_rustc_trait_ref(tcx),
        );
        match selcx.select(&trait_pred) {
            Ok(Some(ImplSource::UserDefined(impl_data))) => Ok(Some(impl_data.impl_def_id)),
            Ok(_) => Ok(None),
            Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
        }
    }

    fn normalize_alias_reft(
        &mut self,
        alias_reft: &AliasReft,
        refine_args: &RefineArgs,
    ) -> QueryResult<Expr> {
        if let Some(impl_def_id) = self.get_impl_id_of_alias_reft(alias_reft)? {
            let impl_trait_ref = self
                .genv
                .impl_trait_ref(impl_def_id)?
                .unwrap()
                .skip_binder();
            let generics = self.tcx().generics_of(impl_def_id);

            let mut subst = TVarSubst::new(generics);
            for (a, b) in iter::zip(&impl_trait_ref.args, &alias_reft.args) {
                subst.generic_args(a, b);
            }
            let args = subst.finish(self.tcx(), generics);

            let tcx = self.tcx();

            let pred = self
                .genv
                .assoc_refinement_def(impl_def_id, alias_reft.name)?
                .instantiate(tcx, &args, &[]);

            pred.apply(refine_args).try_fold_with(self)
        } else {
            Ok(Expr::alias(alias_reft.clone(), refine_args.clone()))
        }
    }

    // TODO: This is a temporary implementation that uses rustc's trait selection when FLUX fails;
    //       The correct thing, e.g for `trait09.rs` is to make sure FLUX's param_env mirrors RUSTC,
    //       by suitably chasing down the super-trait predicates,
    //       see https://github.com/flux-rs/flux/issues/737
    fn normalize_projection_ty_with_rustc(
        &mut self,
        obligation: &AliasTy,
    ) -> QueryResult<SubsetTyCtor> {
        let projection_ty = obligation.to_rustc(self.tcx());
        let cause = ObligationCause::dummy();
        let param_env = self.tcx().param_env(self.def_id);

        let ty = rustc_trait_selection::traits::normalize_projection_ty(
            &mut self.selcx,
            param_env,
            projection_ty,
            cause,
            10,
            &mut vec![],
        )
        .expect_type();
        let rustc_ty = ty.lower(self.tcx()).unwrap();
        Ok(Refiner::default(self.genv, self.def_id)?
            .refine_ty_or_base(&rustc_ty)?
            .expect_base())
    }

    fn normalize_projection_ty(
        &mut self,
        obligation: &AliasTy,
    ) -> QueryResult<(bool, SubsetTyCtor)> {
        let mut candidates = vec![];
        self.assemble_candidates_from_param_env(obligation, &mut candidates);
        self.assemble_candidates_from_trait_def(obligation, &mut candidates)?;
        self.assemble_candidates_from_impls(obligation, &mut candidates)?;

        if candidates.is_empty() {
            let orig_ty =
                BaseTy::Alias(AliasKind::Projection, obligation.clone()).to_subset_ty_ctor();
            let ty = self.normalize_projection_ty_with_rustc(obligation)?;
            return Ok((ty != orig_ty, ty));
        }
        if candidates.len() > 1 {
            bug!("ambiguity when resolving `{obligation:?}` in {:?}", self.def_id);
        }
        let ctor = self.confirm_candidate(candidates.pop().unwrap(), obligation)?;
        Ok((true, ctor))
    }

    fn find_resolved_predicates(
        &self,
        subst: &mut TVarSubst,
        preds: Vec<EarlyBinder<ProjectionPredicate>>,
    ) -> (Vec<ProjectionPredicate>, Vec<EarlyBinder<ProjectionPredicate>>) {
        let mut resolved = vec![];
        let mut unresolved = vec![];
        for pred in preds {
            let term = pred.clone().skip_binder().term;
            let alias_ty = pred.clone().map(|p| p.projection_ty);
            match subst.instantiate_partial(alias_ty) {
                Some(projection_ty) => {
                    let pred = ProjectionPredicate { projection_ty, term };
                    resolved.push(pred);
                }
                None => unresolved.push(pred.clone()),
            }
        }
        (resolved, unresolved)
    }

    // See issue-829*.rs for an example of what this function is for.
    fn resolve_projection_predicates(
        &mut self,
        subst: &mut TVarSubst,
        impl_def_id: DefId,
    ) -> QueryResult {
        let mut projection_preds: Vec<_> = self
            .genv
            .predicates_of(impl_def_id)?
            .skip_binder()
            .predicates
            .iter()
            .filter_map(|pred| {
                if let ClauseKind::Projection(pred) = pred.kind_skipping_binder() {
                    Some(EarlyBinder(pred.clone()))
                } else {
                    None
                }
            })
            .collect();

        while !projection_preds.is_empty() {
            let (resolved, unresolved) = self.find_resolved_predicates(subst, projection_preds);

            if resolved.is_empty() {
                break; // failed: there is some unresolved projection pred!
            }
            for p in resolved {
                let obligation = &p.projection_ty;
                let (_, ctor) = self.normalize_projection_ty(obligation)?;
                // is this right?
                let a = 0;
                subst.tys(&p.term.to_ty(), &ctor.to_ty());
            }
            projection_preds = unresolved;
        }
        Ok(())
    }

    fn confirm_candidate(
        &mut self,
        candidate: Candidate,
        obligation: &AliasTy,
    ) -> QueryResult<SubsetTyCtor> {
        match candidate {
            Candidate::ParamEnv(pred) | Candidate::TraitDef(pred) => Ok(pred.term),
            Candidate::UserDefinedImpl(impl_def_id) => {
                // Given a projection obligation
                //     <IntoIter<{v. i32[v] | v > 0}, Global> as Iterator>::Item
                // and the id of a rust impl block
                //     impl<T, A: Allocator> Iterator for IntoIter<T, A>

                // 1. MATCH the self type of the rust impl block and the flux self type of the obligation
                //    to infer a substitution
                //        IntoIter<{v. i32[v] | v > 0}, Global> MATCH IntoIter<T, A>
                //            => {T -> {v. i32[v] | v > 0}, A -> Global}

                let impl_trait_ref = self
                    .genv
                    .impl_trait_ref(impl_def_id)?
                    .unwrap()
                    .skip_binder();

                let generics = self.tcx().generics_of(impl_def_id);

                let mut subst = TVarSubst::new(generics);
                for (a, b) in iter::zip(&impl_trait_ref.args, &obligation.args) {
                    subst.generic_args(a, b);
                }

                // 2. Gather the ProjectionPredicates and solve them see issue-808.rs
                self.resolve_projection_predicates(&mut subst, impl_def_id)?;

                let args = subst.finish(self.tcx(), generics);

                // 3. Get the associated type in the impl block and apply the substitution to it
                let assoc_type_id = self
                    .tcx()
                    .associated_items(impl_def_id)
                    .in_definition_order()
                    .find(|item| item.trait_item_def_id == Some(obligation.def_id))
                    .map(|item| item.def_id)
                    .unwrap();

                let tcx = self.tcx();
                Ok(self
                    .genv
                    .type_of(assoc_type_id)?
                    .instantiate(tcx, &args, &[])
                    .expect_subset_ty_ctor())
            }
        }
    }

    fn assemble_candidates_from_param_env(
        &self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) {
        assemble_candidates_from_predicates(
            &self.param_env,
            obligation,
            Candidate::ParamEnv,
            candidates,
        );
    }

    fn assemble_candidates_from_trait_def(
        &self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) -> QueryResult {
        if let GenericArg::Base(ctor) = &obligation.args[0]
            && let BaseTy::Alias(AliasKind::Opaque, alias_ty) = ctor.as_bty_skipping_binder()
        {
            // check that alias_ty doesn't have escaping bound vars. Should that be guaranteed by
            // SubsetTy?
            let a = 0;
            let bounds = self.genv.item_bounds(alias_ty.def_id)?.instantiate(
                self.tcx(),
                &alias_ty.args,
                &alias_ty.refine_args,
            );
            assemble_candidates_from_predicates(
                &bounds,
                obligation,
                Candidate::TraitDef,
                candidates,
            );
        }
        Ok(())
    }

    fn assemble_candidates_from_impls(
        &mut self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) -> QueryResult {
        let trait_pred = Obligation::new(
            self.tcx(),
            ObligationCause::dummy(),
            self.rustc_param_env(),
            obligation.to_rustc(self.tcx()).trait_ref(self.tcx()),
        );
        match self.selcx.select(&trait_pred) {
            Ok(Some(ImplSource::UserDefined(impl_data))) => {
                candidates.push(Candidate::UserDefinedImpl(impl_data.impl_def_id));
            }
            Ok(_) => (),
            Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
        }
        Ok(())
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.selcx.tcx()
    }

    fn rustc_param_env(&self) -> rustc_middle::ty::ParamEnv<'tcx> {
        self.selcx.tcx().param_env(self.def_id)
    }
}

fn assemble_candidates_from_predicates(
    predicates: &[Clause],
    obligation: &AliasTy,
    ctor: fn(ProjectionPredicate) -> Candidate,
    candidates: &mut Vec<Candidate>,
) {
    for predicate in predicates {
        if let ClauseKind::Projection(pred) = predicate.kind_skipping_binder() {
            // FIXME(nilehmann) make this matching resilient with respect to syntactic differences
            // in refinements
            if &pred.projection_ty == obligation {
                candidates.push(ctor(pred.clone()));
            }
        }
    }
}

impl FallibleTypeFolder for Normalizer<'_, '_, '_> {
    type Error = QueryErr;

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, Self::Error> {
        match sort {
            Sort::Alias(AliasKind::Weak, alias_ty) => {
                self.genv
                    .normalize_weak_alias_sort(alias_ty)?
                    .try_fold_with(self)
            }
            Sort::Alias(AliasKind::Projection, alias_ty) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let sort = ctor.sort();
                if changed {
                    sort.try_fold_with(self)
                } else {
                    Ok(sort)
                }
            }
            _ => sort.try_super_fold_with(self),
        }
    }

    // As shown in https://github.com/flux-rs/flux/issues/711 one round of `normalize_projections`
    // can replace one projection e.g. `<Rev<Iter<[i32]> as Iterator>::Item` with another e.g.
    // `<Iter<[i32]> as Iterator>::Item` We want to compute a "fixpoint" i.e. keep going until no
    // change, so that e.g. the above is normalized all the way to `i32`, which is what the `changed`
    // is for.
    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, Self::Error> {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Alias(AliasKind::Weak, alias_ty), idx) => {
                Ok(self
                    .genv
                    .type_of(alias_ty.def_id)?
                    .instantiate(self.genv.tcx(), &alias_ty.args, &alias_ty.refine_args)
                    .expect_ctor()
                    .replace_bound_reft(idx))
            }
            TyKind::Indexed(BaseTy::Alias(AliasKind::Projection, alias_ty), idx) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let ty = ctor.replace_bound_reft(idx).to_ty();
                if changed {
                    ty.try_fold_with(self)
                } else {
                    Ok(ty)
                }
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_subset_ty(&mut self, constr: &SubsetTy) -> Result<SubsetTy, Self::Error> {
        match &constr.bty {
            BaseTy::Alias(AliasKind::Weak, _alias_ty) => {
                // change comment if we rename subset ty to constr ty
                let a = 0;
                // Weak aliases are always expanded during conversion. We could in theory normalize
                // them here but we don't guaranatee that type aliases expand to a subset ty. If
                // we ever stop expanding aliases in conv we would need to guarantee that aliases
                // used as a generic base expand to a subset type.
                tracked_span_bug!()
            }
            BaseTy::Alias(AliasKind::Projection, alias_ty) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let ty = ctor.replace_bound_reft(&constr.idx);
                if changed {
                    ty.try_fold_with(self)
                } else {
                    Ok(ty)
                }
            }
            _ => constr.try_super_fold_with(self),
        }
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        if let ExprKind::Alias(alias_pred, refine_args) = expr.kind() {
            self.normalize_alias_reft(alias_pred, refine_args)
        } else {
            expr.try_super_fold_with(self)
        }
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, Self::Error> {
        c.to_rustc(self.tcx())
            .normalize(self.tcx(), self.rustc_param_env())
            .lower(self.tcx())
            .map_err(|e| QueryErr::unsupported(self.def_id, e.into_err()))
    }
}

#[derive(Debug)]
pub enum Candidate {
    UserDefinedImpl(DefId),
    ParamEnv(ProjectionPredicate),
    TraitDef(ProjectionPredicate),
}

#[derive(Debug)]
struct TVarSubst {
    args: Vec<Option<GenericArg>>,
}

impl GenericsSubstDelegate for &TVarSubst {
    type Error = ();

    fn ty_for_param(&mut self, param_ty: rustc_middle::ty::ParamTy) -> Result<Ty, Self::Error> {
        match self.args.get(param_ty.index as usize) {
            Some(Some(GenericArg::Ty(ty))) => Ok(ty.clone()),
            Some(None) => Err(()),
            arg => tracked_span_bug!("expected type for generic parameter, found `{arg:?}`"),
        }
    }

    fn sort_for_param(
        &mut self,
        _param_ty: rustc_middle::ty::ParamTy,
    ) -> Result<super::Sort, Self::Error> {
        tracked_span_bug!()
    }

    fn ctor_for_param(&mut self, _param_ty: rustc_middle::ty::ParamTy) -> super::SubsetTyCtor {
        tracked_span_bug!()
    }

    fn region_for_param(&mut self, _ebr: rustc_middle::ty::EarlyParamRegion) -> Region {
        tracked_span_bug!()
    }

    fn expr_for_param_const(&self, _param_const: rustc_middle::ty::ParamConst) -> Expr {
        tracked_span_bug!()
    }

    fn const_for_param(&mut self, _param: &Const) -> Const {
        tracked_span_bug!()
    }
}

impl TVarSubst {
    fn new(generics: &rustc_middle::ty::Generics) -> Self {
        Self { args: vec![None; generics.count()] }
    }

    fn instantiate_partial<T: TypeFoldable>(&mut self, pred: EarlyBinder<T>) -> Option<T> {
        let mut folder = GenericsSubstFolder::new(&*self, &[]);
        pred.skip_binder().try_fold_with(&mut folder).ok()
    }

    fn finish<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        generics: &'tcx rustc_middle::ty::Generics,
    ) -> Vec<GenericArg> {
        self.args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| {
                if let Some(arg) = arg {
                    arg
                } else {
                    let param = generics.param_at(idx, tcx);
                    tracked_span_bug!("cannot infer substitution for param {param:?}");
                }
            })
            .collect()
    }

    fn generic_args(&mut self, a: &GenericArg, b: &GenericArg) {
        match (a, b) {
            (GenericArg::Ty(a), GenericArg::Ty(b)) => self.tys(a, b),
            (GenericArg::Lifetime(a), GenericArg::Lifetime(b)) => self.regions(*a, *b),
            (GenericArg::Base(a), GenericArg::Base(b)) => {
                self.subset_tys(a, b);
            }
            (GenericArg::Const(a), GenericArg::Const(b)) => self.consts(a, b),
            _ => {}
        }
    }

    fn tys(&mut self, a: &Ty, b: &Ty) {
        if let TyKind::Param(param_ty) = a.kind() {
            if !b.has_escaping_bvars() {
                self.insert_generic_arg(param_ty.index, GenericArg::Ty(b.clone()));
            }
            return;
        }
        let Some(a_bty) = a.as_bty_skipping_existentials() else { return };
        let Some(b_bty) = b.as_bty_skipping_existentials() else { return };
        self.btys(a_bty, b_bty);
    }

    fn subset_tys(&mut self, a: &SubsetTyCtor, b: &SubsetTyCtor) {
        let bty_a = a.as_bty_skipping_binder();
        let bty_b = b.as_bty_skipping_binder();
        if let BaseTy::Param(param_ty) = bty_a {
            if !b.has_escaping_bvars() {
                self.insert_generic_arg(param_ty.index, GenericArg::Base(b.clone()));
            }
        }
        self.btys(bty_a, bty_b);
    }

    fn btys(&mut self, a: &BaseTy, b: &BaseTy) {
        match (a, b) {
            // (BaseTy::Param(param_ty), _) => {
            //     if !b.has_escaping_bvars() {
            //         let sort = b.sort();
            //         let ctor =
            //             Binder::bind_with_sort(SubsetTy::trivial(b.clone(), Expr::nu()), sort);
            //         self.insert_generic_arg(param_ty.index, GenericArg::Base(ctor));
            //     }
            // }
            (BaseTy::Adt(_, a_args), BaseTy::Adt(_, b_args)) => {
                debug_assert_eq!(a_args.len(), b_args.len());
                for (a_arg, b_arg) in iter::zip(a_args, b_args) {
                    self.generic_args(a_arg, b_arg);
                }
            }
            (BaseTy::Array(a_ty, a_n), BaseTy::Array(b_ty, b_n)) => {
                self.tys(a_ty, b_ty);
                self.consts(a_n, b_n);
            }
            (BaseTy::Tuple(a_tys), BaseTy::Tuple(b_tys)) => {
                debug_assert_eq!(a_tys.len(), b_tys.len());
                for (a_ty, b_ty) in iter::zip(a_tys, b_tys) {
                    self.tys(a_ty, b_ty);
                }
            }
            (BaseTy::Ref(a_re, a_ty, _), BaseTy::Ref(b_re, b_ty, _)) => {
                self.regions(*a_re, *b_re);
                self.tys(a_ty, b_ty);
            }
            (BaseTy::Slice(a_ty), BaseTy::Slice(b_ty)) => {
                self.tys(a_ty, b_ty);
            }
            _ => {}
        }
    }

    fn regions(&mut self, a: Region, b: Region) {
        if let Region::ReEarlyParam(ebr) = a {
            self.insert_generic_arg(ebr.index, GenericArg::Lifetime(b));
        }
    }

    fn consts(&mut self, a: &Const, b: &Const) {
        if let super::ConstKind::Param(param_const) = a.kind {
            self.insert_generic_arg(param_const.index, GenericArg::Const(b.clone()));
        }
    }

    fn insert_generic_arg(&mut self, idx: u32, arg: GenericArg) {
        if let Some(old) = &self.args[idx as usize]
            && old != &arg
        {
            tracked_span_bug!("ambiguous substitution: old=`{old:?}`, new: `{arg:?}`");
        }
        self.args[idx as usize].replace(arg);
    }
}
