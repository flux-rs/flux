use std::iter;

use flux_common::{bug, iter::IterExt, tracked_span_bug};
use flux_middle::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self, AliasKind, AliasReft, AliasTy, BaseTy, Binder, Clause, ClauseKind, Const, ConstKind,
        EarlyBinder, Expr, ExprKind, GenericArg, List, ProjectionPredicate, RefineArgs, Region,
        Sort, SubsetTy, SubsetTyCtor, Ty, TyKind,
        fold::{FallibleTypeFolder, TypeFoldable, TypeSuperFoldable, TypeVisitable},
        refining::Refiner,
        subst::{GenericsSubstDelegate, GenericsSubstFolder},
    },
};
use flux_rustc_bridge::{ToRustc, lowering::Lower};
use itertools::izip;
use rustc_hir::def_id::DefId;
use rustc_infer::traits::{ImplSourceUserDefinedData, Obligation, PredicateObligation};
use rustc_middle::{
    traits::{ImplSource, ObligationCause},
    ty::{TyCtxt, Variance},
};
use rustc_trait_selection::{
    solve::deeply_normalize,
    traits::{FulfillmentError, SelectionContext},
};
use rustc_type_ir::TypeVisitableExt;

use crate::{
    fixpoint_encoding::KVarEncoding,
    infer::{InferCtxtAt, InferResult},
    refine_tree::Scope,
};

pub trait NormalizeExt: TypeFoldable {
    fn deeply_normalize(&self, infcx: &mut InferCtxtAt) -> QueryResult<Self>;

    /// Deeply normalize projections but only inside sorts
    fn deeply_normalize_sorts<'tcx>(
        &self,
        def_id: DefId,
        genv: GlobalEnv<'_, 'tcx>,
        infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    ) -> QueryResult<Self>;
}

impl<T: TypeFoldable> NormalizeExt for T {
    fn deeply_normalize(&self, infcx: &mut InferCtxtAt) -> QueryResult<Self> {
        let span = infcx.span;
        let infcx_orig = &mut infcx.infcx;
        let mut infcx = infcx_orig.branch();
        let infcx = infcx.at(span);
        let mut normalizer = Normalizer::new(infcx)?;
        self.erase_regions().try_fold_with(&mut normalizer)
    }

    fn deeply_normalize_sorts<'tcx>(
        &self,
        def_id: DefId,
        genv: GlobalEnv<'_, 'tcx>,
        infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    ) -> QueryResult<Self> {
        let mut normalizer = SortNormalizer::new(def_id, genv, infcx);
        self.erase_regions().try_fold_with(&mut normalizer)
    }
}

struct Normalizer<'a, 'infcx, 'genv, 'tcx> {
    infcx: InferCtxtAt<'a, 'infcx, 'genv, 'tcx>,
    selcx: SelectionContext<'infcx, 'tcx>,
    param_env: List<Clause>,
    scope: Scope,
}

impl<'a, 'infcx, 'genv, 'tcx> Normalizer<'a, 'infcx, 'genv, 'tcx> {
    fn new(infcx: InferCtxtAt<'a, 'infcx, 'genv, 'tcx>) -> QueryResult<Self> {
        let predicates = infcx.genv.predicates_of(infcx.def_id)?;
        let param_env = predicates.instantiate_identity().predicates.clone();
        let selcx = SelectionContext::new(infcx.region_infcx);
        let scope = infcx.cursor().marker().scope().unwrap();
        Ok(Normalizer { infcx, selcx, param_env, scope })
    }

    fn normalize_projection_ty(
        &mut self,
        obligation: &AliasTy,
    ) -> QueryResult<(bool, SubsetTyCtor)> {
        let mut candidates = vec![];
        self.assemble_candidates_from_param_env(obligation, &mut candidates);
        self.assemble_candidates_from_trait_def(obligation, &mut candidates)
            .unwrap_or_else(|err| tracked_span_bug!("{err:?}"));
        self.assemble_candidates_from_impls(obligation, &mut candidates)?;
        if candidates.is_empty() {
            // TODO: This is a temporary hack that uses rustc's trait selection when FLUX fails;
            //       The correct thing, e.g for `trait09.rs` is to make sure FLUX's param_env mirrors RUSTC,
            //       by suitably chasing down the super-trait predicates,
            //       see https://github.com/flux-rs/flux/issues/737
            let (changed, ty_ctor) = normalize_projection_ty_with_rustc(
                self.genv(),
                self.def_id(),
                self.infcx.region_infcx,
                obligation,
            )?;
            return Ok((changed, ty_ctor));
        }
        if candidates.len() > 1 {
            bug!("ambiguity when resolving `{obligation:?}` in {:?}", self.def_id());
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
            .genv()
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
                subst.subset_tys(&p.term, &ctor);
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
        let tcx = self.tcx();
        match candidate {
            Candidate::ParamEnv(pred) | Candidate::TraitDef(pred) => {
                let rustc_obligation = obligation.to_rustc(tcx);
                let parent_id = rustc_obligation.trait_ref(tcx).def_id;
                // Do fn-subtyping if the candidate was a fn-trait
                if tcx.is_fn_trait(parent_id) {
                    let res = self
                        .fn_subtype_projection_ty(pred, obligation)
                        .unwrap_or_else(|err| tracked_span_bug!("{err:?}"));
                    Ok(res)
                } else {
                    Ok(pred.skip_binder().term)
                }
            }
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
                    .genv()
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

                let args = subst.finish(self.tcx(), generics)?;

                // 3. Get the associated type in the impl block and apply the substitution to it
                let assoc_type_id = tcx
                    .associated_items(impl_def_id)
                    .in_definition_order()
                    .find(|item| item.trait_item_def_id() == Some(obligation.def_id))
                    .map(|item| item.def_id)
                    .ok_or_else(|| {
                        query_bug!("no associated type for {obligation:?} in impl {impl_def_id:?}")
                    })?;
                Ok(self
                    .genv()
                    .type_of(assoc_type_id)?
                    .instantiate(tcx, &args, &[])
                    .expect_subset_ty_ctor())
            }
        }
    }

    fn fn_subtype_projection_ty(
        &mut self,
        actual: Binder<ProjectionPredicate>,
        oblig: &AliasTy,
    ) -> InferResult<SubsetTyCtor> {
        // Step 1: bs <- unpack(b1...)
        let obligs: Vec<_> = oblig
            .args
            .iter()
            .map(|arg| {
                match arg {
                    GenericArg::Ty(ty) => GenericArg::Ty(self.infcx.unpack(ty)),
                    GenericArg::Base(ctor) => GenericArg::Ty(self.infcx.unpack(&ctor.to_ty())),
                    _ => arg.clone(),
                }
            })
            .collect();

        let span = self.infcx.span;
        let mut infcx = self.infcx.at(span);

        let actual = infcx.ensure_resolved_evars(|infcx| {
            // Step 2: as <- fresh(a1...)
            let actual = actual
                .replace_bound_vars(
                    |_| rty::ReErased,
                    |sort, mode| infcx.fresh_infer_var(sort, mode),
                )
                .deeply_normalize(infcx)?;

            let actuals = actual.projection_ty.args.iter().map(|arg| {
                match arg {
                    GenericArg::Base(ctor) => GenericArg::Ty(ctor.to_ty()),
                    _ => arg.clone(),
                }
            });

            // Step 3: bs <: as
            for (a, b) in izip!(actuals.skip(1), obligs.iter().skip(1)) {
                infcx.subtyping_generic_args(
                    Variance::Contravariant,
                    &a,
                    b,
                    crate::infer::ConstrReason::Predicate,
                )?;
            }
            Ok(actual)
        })?;
        // Step 4: check all evars are solved, plug back into ProjectionPredicate
        let actual = infcx.fully_resolve_evars(&actual);

        // Step 5: generate "fresh" type for actual.term,
        let oblig_term = actual.term.with_holes().replace_holes(|binders, kind| {
            assert!(kind == rty::HoleKind::Pred);
            let scope = &self.scope;
            infcx.fresh_kvar_in_scope(binders, scope, KVarEncoding::Conj)
        });

        // Step 6: subtyping obligation on output
        infcx.subtyping(
            &actual.term.to_ty(),
            &oblig_term.to_ty(),
            crate::infer::ConstrReason::Predicate,
        )?;
        // Ok(ProjectionPredicate { projection_ty: actual.projection_ty, term: oblig_term })
        Ok(oblig_term)
    }

    fn assemble_candidates_from_predicates(
        &mut self,
        predicates: &List<Clause>,
        obligation: &AliasTy,
        ctor: fn(Binder<ProjectionPredicate>) -> Candidate,
        candidates: &mut Vec<Candidate>,
    ) {
        let tcx = self.tcx();
        let rustc_obligation = obligation.to_rustc(tcx);

        for predicate in predicates {
            if let Some(pred) = predicate.as_projection_clause()
                && pred.skip_binder_ref().projection_ty.to_rustc(tcx) == rustc_obligation
            {
                candidates.push(ctor(pred));
            }
        }
    }

    fn assemble_candidates_from_param_env(
        &mut self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) {
        let predicates = self.param_env.clone();
        self.assemble_candidates_from_predicates(
            &predicates,
            obligation,
            Candidate::ParamEnv,
            candidates,
        );
    }

    fn assemble_candidates_from_trait_def(
        &mut self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) -> InferResult {
        if let GenericArg::Base(ctor) = &obligation.args[0]
            && let BaseTy::Alias(AliasKind::Opaque, alias_ty) = ctor.as_bty_skipping_binder()
        {
            debug_assert!(!alias_ty.has_escaping_bvars());
            let bounds = self.genv().item_bounds(alias_ty.def_id)?.instantiate(
                self.tcx(),
                &alias_ty.args,
                &alias_ty.refine_args,
            );
            self.assemble_candidates_from_predicates(
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
        let trait_ref = obligation.to_rustc(self.tcx()).trait_ref(self.tcx());
        let trait_ref = self.tcx().erase_and_anonymize_regions(trait_ref);
        let trait_pred = Obligation::new(
            self.tcx(),
            ObligationCause::dummy(),
            self.rustc_param_env(),
            trait_ref,
        );
        // FIXME(nilehmann) This is a patch to not panic inside rustc so we are
        // able to catch the bug
        if trait_pred.has_escaping_bound_vars() {
            tracked_span_bug!();
        }
        match self.selcx.select(&trait_pred) {
            Ok(Some(ImplSource::UserDefined(impl_data))) => {
                candidates.push(Candidate::UserDefinedImpl(impl_data.impl_def_id));
            }
            Ok(_) => (),
            Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
        }
        Ok(())
    }

    fn def_id(&self) -> DefId {
        self.infcx.def_id
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.infcx.genv
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.selcx.tcx()
    }

    fn rustc_param_env(&self) -> rustc_middle::ty::ParamEnv<'tcx> {
        self.selcx.tcx().param_env(self.def_id())
    }
}

impl FallibleTypeFolder for Normalizer<'_, '_, '_, '_> {
    type Error = QueryErr;

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, Self::Error> {
        match sort {
            Sort::Alias(AliasKind::Free, alias_ty) => {
                self.genv()
                    .normalize_free_alias_sort(alias_ty)?
                    .try_fold_with(self)
            }
            Sort::Alias(AliasKind::Projection, alias_ty) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let sort = ctor.sort();
                if changed { sort.try_fold_with(self) } else { Ok(sort) }
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
            TyKind::Indexed(BaseTy::Alias(AliasKind::Free, alias_ty), idx) => {
                Ok(self
                    .genv()
                    .type_of(alias_ty.def_id)?
                    .instantiate(self.tcx(), &alias_ty.args, &alias_ty.refine_args)
                    .expect_ctor()
                    .replace_bound_reft(idx))
            }
            TyKind::Indexed(BaseTy::Alias(AliasKind::Projection, alias_ty), idx) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let ty = ctor.replace_bound_reft(idx).to_ty();
                if changed { ty.try_fold_with(self) } else { Ok(ty) }
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_subset_ty(&mut self, sty: &SubsetTy) -> Result<SubsetTy, Self::Error> {
        match &sty.bty {
            BaseTy::Alias(AliasKind::Free, _alias_ty) => {
                // Weak aliases are always expanded during conversion. We could in theory normalize
                // them here but we don't guaranatee that type aliases expand to a subset ty. If we
                // ever stop expanding aliases during conv we would need to guarantee that aliases
                // used as a generic base expand to a subset type.
                tracked_span_bug!()
            }
            BaseTy::Alias(AliasKind::Projection, alias_ty) => {
                let (changed, ctor) = self.normalize_projection_ty(alias_ty)?;
                let ty = ctor.replace_bound_reft(&sty.idx).strengthen(&sty.pred);
                if changed { ty.try_fold_with(self) } else { Ok(ty) }
            }
            _ => sty.try_super_fold_with(self),
        }
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        if let ExprKind::Alias(alias_pred, refine_args) = expr.kind() {
            let (changed, e) = normalize_alias_reft(
                self.genv(),
                self.def_id(),
                self.selcx.infcx,
                alias_pred,
                refine_args,
            )?;
            if changed { e.try_fold_with(self) } else { Ok(e) }
        } else {
            expr.try_super_fold_with(self)
        }
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, Self::Error> {
        let c = c.to_rustc(self.tcx());
        rustc_trait_selection::traits::evaluate_const(self.selcx.infcx, c, self.rustc_param_env())
            .lower(self.tcx())
            .map_err(|e| QueryErr::unsupported(self.def_id(), e.into_err()))
    }
}

#[derive(Debug)]
pub enum Candidate {
    UserDefinedImpl(DefId),
    ParamEnv(Binder<ProjectionPredicate>),
    TraitDef(Binder<ProjectionPredicate>),
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

    fn sort_for_param(&mut self, param_ty: rustc_middle::ty::ParamTy) -> Result<Sort, Self::Error> {
        match self.args.get(param_ty.index as usize) {
            Some(Some(GenericArg::Base(ctor))) => Ok(ctor.sort()),
            Some(None) => Err(()),
            arg => tracked_span_bug!("expected type for generic parameter, found `{arg:?}`"),
        }
    }

    fn ctor_for_param(
        &mut self,
        param_ty: rustc_middle::ty::ParamTy,
    ) -> Result<SubsetTyCtor, Self::Error> {
        match self.args.get(param_ty.index as usize) {
            Some(Some(GenericArg::Base(ctor))) => Ok(ctor.clone()),
            Some(None) => Err(()),
            arg => tracked_span_bug!("expected type for generic parameter, found `{arg:?}`"),
        }
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

struct SortNormalizer<'infcx, 'genv, 'tcx> {
    def_id: DefId,
    infcx: &'infcx rustc_infer::infer::InferCtxt<'tcx>,
    genv: GlobalEnv<'genv, 'tcx>,
}

impl<'infcx, 'genv, 'tcx> SortNormalizer<'infcx, 'genv, 'tcx> {
    fn new(
        def_id: DefId,
        genv: GlobalEnv<'genv, 'tcx>,
        infcx: &'infcx rustc_infer::infer::InferCtxt<'tcx>,
    ) -> Self {
        Self { def_id, infcx, genv }
    }
}

impl FallibleTypeFolder for SortNormalizer<'_, '_, '_> {
    type Error = QueryErr;
    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, Self::Error> {
        match sort {
            Sort::Alias(AliasKind::Free, alias_ty) => {
                self.genv
                    .normalize_free_alias_sort(alias_ty)?
                    .try_fold_with(self)
            }
            Sort::Alias(AliasKind::Projection, alias_ty) => {
                let (changed, ctor) = normalize_projection_ty_with_rustc(
                    self.genv,
                    self.def_id,
                    self.infcx,
                    alias_ty,
                )?;
                let sort = ctor.sort();
                if changed { sort.try_fold_with(self) } else { Ok(sort) }
            }
            _ => sort.try_super_fold_with(self),
        }
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
    ) -> QueryResult<Vec<GenericArg>> {
        self.args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| {
                if let Some(arg) = arg {
                    Ok(arg)
                } else {
                    let param = generics.param_at(idx, tcx);
                    Err(QueryErr::bug(
                        None,
                        format!("cannot infer substitution for {param:?} at index {idx}"),
                    ))
                }
            })
            .try_collect_vec()
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
        } else {
            let Some(a_bty) = a.as_bty_skipping_existentials() else { return };
            let Some(b_bty) = b.as_bty_skipping_existentials() else { return };
            self.btys(a_bty, b_bty);
        }
    }

    fn subset_tys(&mut self, a: &SubsetTyCtor, b: &SubsetTyCtor) {
        let bty_a = a.as_bty_skipping_binder();
        let bty_b = b.as_bty_skipping_binder();
        if let BaseTy::Param(param_ty) = bty_a {
            if !b.has_escaping_bvars() {
                self.insert_generic_arg(param_ty.index, GenericArg::Base(b.clone()));
            }
        } else {
            self.btys(bty_a, bty_b);
        }
    }

    fn btys(&mut self, a: &BaseTy, b: &BaseTy) {
        match (a, b) {
            (BaseTy::Param(param_ty), _) => {
                if !b.has_escaping_bvars() {
                    let sort = b.sort();
                    let ctor =
                        Binder::bind_with_sort(SubsetTy::trivial(b.clone(), Expr::nu()), sort);
                    self.insert_generic_arg(param_ty.index, GenericArg::Base(ctor));
                }
            }
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
        if let ConstKind::Param(param_const) = a.kind {
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

/// Normalize an [`rty::AliasTy`] by converting it to rustc, normalizing it using rustc api, and
/// then mapping the result back to `rty`. This will lose refinements and it should only be used
/// to normalize sorts because they should only contain unrefined types. However, we are also using
/// it as a hack to normalize types in cases where we fail to collect a candidate, this is unsound
/// and should be removed.
///
/// [`rty::AliasTy`]: AliasTy
fn normalize_projection_ty_with_rustc<'tcx>(
    genv: GlobalEnv<'_, 'tcx>,
    def_id: DefId,
    infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    obligation: &AliasTy,
) -> QueryResult<(bool, SubsetTyCtor)> {
    let tcx = genv.tcx();
    let projection_ty = obligation.to_rustc(tcx);
    let projection_ty = tcx.erase_and_anonymize_regions(projection_ty);
    let cause = ObligationCause::dummy();
    let param_env = tcx.param_env(def_id);

    let pre_ty = projection_ty.to_ty(tcx);
    let at = infcx.at(&cause, param_env);
    let ty = deeply_normalize::<rustc_middle::ty::Ty<'tcx>, FulfillmentError>(at, pre_ty)
        .map_err(|err| query_bug!("{err:?}"))?;

    let changed = pre_ty != ty;
    let rustc_ty = ty.lower(tcx).map_err(|reason| query_bug!("{reason:?}"))?;

    Ok((
        changed,
        Refiner::default_for_item(genv, def_id)?
            .refine_ty_or_base(&rustc_ty)?
            .expect_base(),
    ))
}

/// Do one step of normalization, unfolding associated refinements if they are concrete.
///
/// Use this if you are about to match structurally on an [`ExprKind`] and you need associated
/// refinements to be normalized.
pub fn structurally_normalize_expr(
    genv: GlobalEnv,
    def_id: DefId,
    infcx: &rustc_infer::infer::InferCtxt,
    expr: &Expr,
) -> QueryResult<Expr> {
    if let ExprKind::Alias(alias_pred, refine_args) = expr.kind() {
        let (_, e) = normalize_alias_reft(genv, def_id, infcx, alias_pred, refine_args)?;
        Ok(e)
    } else {
        Ok(expr.clone())
    }
}

/// Normalizes an [`AliasReft`]. This uses the trait solver to find the [`ImplSourceUserDefinedData`]
/// and uses the `args` there, which we map back to Flux via refining. This loses refinements,
/// but that's fine because [`AliasReft`] should not rely on refinements for trait solving.
fn normalize_alias_reft(
    genv: GlobalEnv,
    def_id: DefId,
    infcx: &rustc_infer::infer::InferCtxt,
    alias_reft: &AliasReft,
    refine_args: &RefineArgs,
) -> QueryResult<(bool, Expr)> {
    let is_final = genv.assoc_refinement(alias_reft.assoc_id)?.final_;
    if is_final {
        let e = genv
            .default_assoc_refinement_body(alias_reft.assoc_id)?
            .unwrap_or_else(|| {
                bug!("final associated refinement without body - should be caught in desugar")
            })
            .instantiate(genv.tcx(), &alias_reft.args, &[])
            .apply(refine_args);
        Ok((true, e))
    } else if let Some(impl_data) = get_impl_data_for_alias_reft(infcx, def_id, alias_reft)? {
        let tcx = infcx.tcx;
        let impl_def_id = impl_data.impl_def_id;
        let args = Refiner::default_for_item(genv, def_id)?.refine_generic_args(
            impl_def_id,
            &impl_data
                .args
                .lower(tcx)
                .map_err(|reason| query_bug!("{reason:?}"))?,
        )?;
        let e = genv
            .assoc_refinement_body_for_impl(alias_reft.assoc_id, impl_def_id)?
            .instantiate(tcx, &args, &[])
            .apply(refine_args);
        Ok((true, e))
    } else {
        Ok((false, Expr::alias(alias_reft.clone(), refine_args.clone())))
    }
}

fn get_impl_data_for_alias_reft<'tcx>(
    infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    def_id: DefId,
    alias_reft: &AliasReft,
) -> QueryResult<Option<ImplSourceUserDefinedData<'tcx, PredicateObligation<'tcx>>>> {
    let tcx = infcx.tcx;
    let mut selcx = SelectionContext::new(infcx);
    let trait_ref = alias_reft.to_rustc_trait_ref(tcx);
    let trait_ref = tcx.erase_and_anonymize_regions(trait_ref);
    let trait_pred =
        Obligation::new(tcx, ObligationCause::dummy(), tcx.param_env(def_id), trait_ref);
    match selcx.select(&trait_pred) {
        Ok(Some(ImplSource::UserDefined(impl_data))) => Ok(Some(impl_data)),
        Ok(_) => Ok(None),
        Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
    }
}
