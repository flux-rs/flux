use std::{cell::RefCell, iter};

use flux_common::bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    queries::QueryErr,
    rty::{
        self, evars::EVarSol, fold::TypeFoldable, AliasTy, BaseTy, Binder, CoroutineObligPredicate,
        ESpan, EVarGen, EarlyBinder, Ensures, Expr, ExprKind, FnOutput, GenericArg, HoleKind,
        InferMode, Lambda, Mutability, PolyFnSig, PolyVariant, PtrKind, Ref, Sort, Ty, TyKind, Var,
    },
    rustc::mir::{BasicBlock, Place},
};
use itertools::{izip, Itertools};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::{BoundRegionConversionTime, RegionVariableOrigin};
use rustc_middle::ty::{BoundRegionKind, Variance};
use rustc_span::Span;

use crate::{
    checker::errors::CheckerErrKind,
    fixpoint_encoding::KVarEncoding,
    refine_tree::{RefineCtxt, Scope, Snapshot},
    type_env::TypeEnv,
};

type Result<T = ()> = std::result::Result<T, CheckerErrKind>;

pub struct ConstrGen<'a, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    def_id: DefId,
    refparams: &'a [Expr],
    kvar_gen: Box<dyn KVarGen + 'a>,
    span: Span,
}

pub(crate) struct Obligations {
    pub(crate) predicates: List<rty::Clause>,
    /// Snapshot of the refinement subtree where the obligations should be checked
    pub(crate) snapshot: Snapshot,
}

pub trait KVarGen {
    fn fresh(&self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr;
}

pub(crate) struct InferCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    def_id: DefId,
    refparams: &'a [Expr],
    kvar_gen: &'a mut (dyn KVarGen + 'a),
    evar_gen: RefCell<EVarGen<Scope>>,
    tag: Tag,
    obligs: Vec<rty::Clause>,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Tag {
    pub reason: ConstrReason,
    pub src_span: Span,
    pub dst_span: Option<ESpan>,
}

impl Tag {
    pub fn new(reason: ConstrReason, span: Span) -> Self {
        Self { reason, src_span: span, dst_span: None }
    }

    pub fn with_dst(self, dst_span: Option<ESpan>) -> Self {
        Self { dst_span, ..self }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum ConstrReason {
    Call,
    Assign,
    Ret,
    Fold,
    Assert(&'static str),
    Div,
    Rem,
    Goto(BasicBlock),
    Overflow,
    Other,
}

impl<'a, 'genv, 'tcx> ConstrGen<'a, 'genv, 'tcx> {
    pub fn new<G>(
        genv: GlobalEnv<'genv, 'tcx>,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'a [Expr],
        kvar_gen: G,
        span: Span,
    ) -> Self
    where
        G: KVarGen + 'a,
    {
        ConstrGen { genv, region_infcx, def_id, refparams, kvar_gen: Box::new(kvar_gen), span }
    }

    pub(crate) fn check_pred(
        &self,
        rcx: &mut RefineCtxt,
        pred: impl Into<Expr>,
        reason: ConstrReason,
    ) {
        rcx.check_pred(pred, Tag::new(reason, self.span));
    }

    pub(crate) fn subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty1: &Ty,
        ty2: &Ty,
        reason: ConstrReason,
    ) {
        let mut infcx = self.infcx(rcx, reason);
        let _ = infcx.subtyping(rcx, ty1, ty2);
        rcx.replace_evars(&infcx.solve().unwrap());
    }

    pub(crate) fn pack_closure_operands(&mut self, env: &mut TypeEnv, operands: &[Ty]) -> List<Ty> {
        operands
            .iter()
            .map(|ty| {
                match ty.kind() {
                    TyKind::Ptr(PtrKind::Mut(region), path) => {
                        let ty = env.get(path);
                        rty::Ty::mk_ref(*region, ty, Mutability::Mut)
                    }
                    _ => ty.clone(),
                }
            })
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_fn_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        callee_def_id: Option<DefId>,
        fn_sig: EarlyBinder<PolyFnSig>,
        generic_args: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<(Binder<FnOutput>, Obligations)> {
        let genv = self.genv;
        let span = self.span;

        let mut infcx = self.infcx(rcx, ConstrReason::Call);
        let snapshot = rcx.snapshot();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        // Generate fresh inference variables for refinement arguments
        let refine_args = infcx.instantiate_refine_args(genv, callee_def_id)?;

        // Instantiate function signature and normalize it
        let fn_sig = fn_sig
            .instantiate(genv.tcx(), &generic_args, &refine_args)
            .replace_bound_vars(
                |br| infcx.next_bound_region_var(span, br.kind, BoundRegionConversionTime::FnCall),
                |sort, mode| infcx.fresh_infer_var(sort, mode),
            );

        let fn_sig = fn_sig.normalize_projections(
            genv,
            infcx.region_infcx,
            infcx.def_id,
            infcx.refparams,
        )?;

        let obligs = if let Some(did) = callee_def_id {
            mk_obligations(genv, did, &generic_args, &refine_args)?
        } else {
            List::empty()
        };

        // Check requires predicates
        for requires in fn_sig.requires() {
            infcx.check_pred(rcx, requires);
        }

        // Check arguments
        for (actual, formal) in iter::zip(actuals, fn_sig.inputs()) {
            let (formal, pred) = formal.unconstr();
            infcx.check_pred(rcx, &pred);
            // TODO(pack-closure): Generalize/refactor to reuse for mutable closures
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path1), TyKind::StrgRef(_, path2, ty2)) => {
                    let ty1 = env.get(path1);
                    infcx.unify_exprs(&path1.to_expr(), &path2.to_expr());
                    infcx.subtyping(rcx, &ty1, ty2)?;
                }
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env.block_with(genv, path, bound.clone())?;
                    infcx.subtyping(rcx, &ty, bound)?;
                }
                _ => infcx.subtyping(rcx, actual, &formal)?,
            }
        }

        // check (non-closure) obligations -- the closure ones are handled in `checker` since
        // as we have to recursively walk over their def_id bodies.
        for pred in &obligs {
            if let rty::ClauseKind::Projection(projection_pred) = pred.kind() {
                let impl_elem = Ty::projection(projection_pred.projection_ty)
                    .normalize_projections(
                        infcx.genv,
                        infcx.region_infcx,
                        infcx.def_id,
                        infcx.refparams,
                    )?;
                let term = projection_pred.term.normalize_projections(
                    infcx.genv,
                    infcx.region_infcx,
                    infcx.def_id,
                    infcx.refparams,
                )?;

                // TODO: does this really need to be invariant? https://github.com/flux-rs/flux/pull/478#issuecomment-1654035374
                infcx.subtyping(rcx, &impl_elem, &term)?;
                infcx.subtyping(rcx, &term, &impl_elem)?;
            }
        }
        // Replace evars
        let evars_sol = infcx.solve()?;
        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);
        let output = fn_sig.output().replace_evars(&evars_sol);

        Ok((output, Obligations::new(obligs, snapshot)))
    }

    pub(crate) fn check_ret(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        output: &Binder<FnOutput>,
    ) -> Result<Obligations> {
        let ret_place_ty = env.lookup_place(self.genv, rcx, Place::RETURN)?;

        let mut infcx = self.infcx(rcx, ConstrReason::Ret);

        let output =
            output.replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));

        infcx.subtyping(rcx, &ret_place_ty, &output.ret)?;
        for constraint in &output.ensures {
            infcx.check_ensures(rcx, env, constraint)?;
        }

        let obligs = infcx.obligations();

        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(Obligations::new(obligs.into(), rcx.snapshot()))
    }

    pub(crate) fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: EarlyBinder<PolyVariant>,
        generic_args: &[GenericArg],
        fields: &[Ty],
    ) -> Result<Ty> {
        let tcx = self.genv.tcx();
        // rn we are only calling `check_constructor` when folding so we mark this as a folding error.
        let mut infcx = self.infcx(rcx, ConstrReason::Fold);

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(tcx, &generic_args, &[])
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            infcx.subtyping(rcx, actual, formal)?;
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret().replace_evars(&evars_sol))
    }

    pub(crate) fn check_mk_array(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        args: &[Ty],
        arr_ty: Ty,
    ) -> Result<Ty> {
        let mut infcx = self.infcx(rcx, ConstrReason::Other);

        let arr_ty =
            arr_ty.replace_holes(|binders, kind| infcx.fresh_infer_var_for_hole(binders, kind));

        let (arr_ty, pred) = arr_ty.unconstr();
        infcx.check_pred(rcx, &pred);

        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env.block_with(infcx.genv, path, bound.clone())?;
                    infcx.subtyping(rcx, &ty, bound)?;
                }
                _ => infcx.subtyping(rcx, ty, &arr_ty)?,
            }
        }
        rcx.replace_evars(&infcx.solve()?);

        Ok(Ty::array(arr_ty, rty::Const::from_usize(self.genv.tcx(), args.len())))
    }

    pub(crate) fn infcx(
        &mut self,
        rcx: &RefineCtxt,
        reason: ConstrReason,
    ) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt::new(
            self.genv,
            self.region_infcx,
            self.def_id,
            self.refparams,
            rcx,
            &mut *self.kvar_gen,
            Tag::new(reason, self.span),
        )
    }
}

impl<'a, 'genv, 'tcx> InferCtxt<'a, 'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'a [Expr],
        rcx: &RefineCtxt,
        kvar_gen: &'a mut (dyn KVarGen + 'a),
        tag: Tag,
    ) -> Self {
        let mut evar_gen = EVarGen::default();
        evar_gen.enter_context(rcx.scope());
        Self {
            genv,
            region_infcx,
            def_id,
            refparams,
            kvar_gen,
            evar_gen: RefCell::new(evar_gen),
            tag,
            obligs: Vec::new(),
        }
    }

    fn obligations(&self) -> Vec<rty::Clause> {
        self.obligs.clone()
    }

    fn insert_obligations(&mut self, obligs: Vec<rty::Clause>) {
        self.obligs.extend(obligs);
    }

    fn push_scope(&mut self, rcx: &RefineCtxt) {
        self.evar_gen.borrow_mut().enter_context(rcx.scope());
    }

    fn pop_scope(&mut self) {
        self.evar_gen.borrow_mut().exit_context();
    }

    fn instantiate_refine_args(
        &mut self,
        genv: GlobalEnv,
        callee_def_id: Option<DefId>,
    ) -> Result<Vec<Expr>> {
        if let Some(callee_id) = callee_def_id {
            Ok(genv
                .refinement_generics_of(callee_id)?
                .collect_all_params(genv, |param| self.fresh_infer_var(&param.sort, param.mode))?)
        } else {
            Ok(vec![])
        }
    }

    fn instantiate_generic_args(&mut self, args: &[GenericArg]) -> Vec<GenericArg> {
        args.iter()
            .map(|a| a.replace_holes(|binders, kind| self.fresh_infer_var_for_hole(binders, kind)))
            .collect_vec()
    }

    fn next_region_var(&self, origin: RegionVariableOrigin) -> rty::Region {
        rty::ReVar(self.region_infcx.next_region_var(origin).as_var())
    }

    fn next_bound_region_var(
        &self,
        span: Span,
        kind: BoundRegionKind,
        conversion_time: BoundRegionConversionTime,
    ) -> rty::Region {
        self.next_region_var(RegionVariableOrigin::BoundRegion(span, kind, conversion_time))
    }

    pub(crate) fn fresh_infer_var(&self, sort: &Sort, mode: InferMode) -> Expr {
        match mode {
            InferMode::KVar => {
                let fsort = sort.expect_func().expect_mono();
                let inputs = List::from_slice(fsort.inputs());
                let kvar = self.fresh_kvar(&[inputs.clone()], KVarEncoding::Single);
                Expr::abs(Lambda::with_sorts(kvar, &inputs, fsort.output().clone()))
            }
            InferMode::EVar => self.fresh_evars(sort),
        }
    }

    fn fresh_infer_var_for_hole(&mut self, binders: &[List<Sort>], kind: HoleKind) -> Expr {
        match kind {
            HoleKind::Pred => self.fresh_kvar(binders, KVarEncoding::Conj),
            HoleKind::Expr(sort) => {
                assert!(binders.is_empty(), "TODO: implement evars under binders");
                self.fresh_evars(&sort)
            }
        }
    }

    pub(crate) fn fresh_kvar(&self, sorts: &[List<Sort>], encoding: KVarEncoding) -> Expr {
        self.kvar_gen.fresh(sorts, encoding)
    }

    fn fresh_evars(&self, sort: &Sort) -> Expr {
        let mut evar_gen = self.evar_gen.borrow_mut();
        Expr::fold_sort(sort, |_| Expr::evar(evar_gen.fresh_in_current()))
    }

    pub(crate) fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>) {
        rcx.check_pred(pred, self.tag);
    }

    fn check_ensures(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        ensures: &Ensures,
    ) -> Result {
        let rcx = &mut rcx.branch();
        match ensures {
            Ensures::Type(path, ty) => {
                let actual_ty = env.get(path);
                self.subtyping(rcx, &actual_ty, ty)
            }
            Ensures::Pred(e) => {
                rcx.check_pred(e, self.tag);
                Ok(())
            }
        }
    }

    pub(crate) fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) -> Result {
        let rcx = &mut rcx.branch();

        // We *fully* unpack the lhs before continuing to be able to prove goals like this
        // ∃a. (i32[a], ∃b. {i32[b] | a > b})} <: ∃a,b. ({i32[a] | b < a}, i32[b])
        // See S4.5 in https://arxiv.org/pdf/2209.13000v1.pdf
        let ty1 = rcx.unpack(ty1);

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(..), _) => {
                bug!("existentials should be removed by the unpack");
            }
            (TyKind::Constr(..), _) => {
                bug!("constraint types should removed by the unpack");
            }
            (_, TyKind::Exists(ty2)) => {
                self.push_scope(rcx);
                let ty2 =
                    ty2.replace_bound_refts_with(|sort, mode, _| self.fresh_infer_var(sort, mode));
                self.subtyping(rcx, &ty1, &ty2)?;
                self.pop_scope();
                Ok(())
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.bty_subtyping(rcx, bty1, bty2)?;
                self.idx_eq(rcx, idx1, idx2);
                Ok(())
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
                Ok(())
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ok(())
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
                Ok(())
            }
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2.clone(), self.tag);
                self.subtyping(rcx, &ty1, ty2)
            }
            (TyKind::Downcast(.., fields1), TyKind::Downcast(.., fields2)) => {
                debug_assert_eq!(fields1.len(), fields2.len());
                for (field1, field2) in iter::zip(fields1, fields2) {
                    self.subtyping(rcx, field1, field2)?;
                }
                Ok(())
            }
            (_, TyKind::Alias(rty::AliasKind::Opaque, alias_ty)) => {
                if let TyKind::Alias(rty::AliasKind::Opaque, alias_ty1) = ty1.kind() {
                    debug_assert_eq!(alias_ty1.refine_args.len(), alias_ty.refine_args.len());
                    iter::zip(alias_ty1.refine_args.iter(), alias_ty.refine_args.iter())
                        .for_each(|(e1, e2)| self.unify_exprs(e1, e2));
                }

                self.opaque_subtyping(rcx, &ty1, alias_ty)
            }
            (
                TyKind::Alias(rty::AliasKind::Projection, alias_ty1),
                TyKind::Alias(rty::AliasKind::Projection, alias_ty2),
            ) => {
                debug_assert_eq!(alias_ty1, alias_ty2);
                Ok(())
            }
            _ => Err(QueryErr::bug(format!("incompatible types: `{ty1:?}` - `{ty2:?}`")))?,
        }
    }

    fn bty_subtyping(&mut self, rcx: &mut RefineCtxt, bty1: &BaseTy, bty2: &BaseTy) -> Result {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                Ok(())
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                Ok(())
            }
            (BaseTy::Adt(adt1, args1), BaseTy::Adt(adt2, args2)) => {
                debug_assert_eq!(adt1.did(), adt2.did());
                debug_assert_eq!(args1.len(), args2.len());
                let variances = self.genv.variances_of(adt1.did());
                for (variance, ty1, ty2) in izip!(variances, args1.iter(), args2.iter()) {
                    self.generic_arg_subtyping(rcx, *variance, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ok(())
            }

            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => self.subtyping(rcx, ty1, ty2),
            (BaseTy::Ref(_, ty1, Mutability::Mut), BaseTy::Ref(_, ty2, Mutability::Mut)) => {
                self.subtyping(rcx, ty1, ty2)?;
                self.subtyping(rcx, ty2, ty1)
            }
            (BaseTy::Ref(_, ty1, Mutability::Not), BaseTy::Ref(_, ty2, Mutability::Not)) => {
                self.subtyping(rcx, ty1, ty2)
            }
            (BaseTy::Tuple(tys1), BaseTy::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1, len2);
                self.subtyping(rcx, ty1, ty2)
            }
            (BaseTy::Param(param1), BaseTy::Param(param2)) => {
                debug_assert_eq!(param1, param2);
                Ok(())
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtr(_, _), BaseTy::RawPtr(_, _)) => Ok(()),
            (BaseTy::Dynamic(preds1, _), BaseTy::Dynamic(preds2, _)) => {
                assert_eq!(preds1, preds2);
                Ok(())
            }
            (BaseTy::Closure(did1, tys1), BaseTy::Closure(did2, tys2)) if did1 == did2 => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            _ => Err(QueryErr::bug(format!("incompatible base types: `{bty1:?}` - `{bty2:?}`")))?,
        }
    }

    fn project_bty(&mut self, self_ty: &Ty, def_id: DefId) -> Result<Ty> {
        let args = List::singleton(GenericArg::Ty(self_ty.clone()));
        let alias_ty = rty::AliasTy::new(def_id, args, List::empty());
        Ok(Ty::projection(alias_ty).normalize_projections(
            self.genv,
            self.region_infcx,
            self.def_id,
            self.refparams,
        )?)
    }

    fn opaque_subtyping(&mut self, rcx: &mut RefineCtxt, ty: &Ty, alias_ty: &AliasTy) -> Result {
        if let Some(BaseTy::Coroutine(def_id, resume_ty, upvar_tys)) =
            ty.as_bty_skipping_existentials()
        {
            let obligs = mk_generator_obligations(
                self.genv,
                def_id,
                resume_ty,
                upvar_tys,
                &alias_ty.def_id,
            )?;
            self.insert_obligations(obligs);
        } else {
            let bounds = self
                .genv
                .item_bounds(alias_ty.def_id)?
                .instantiate_identity(self.refparams);
            for clause in &bounds {
                if let rty::ClauseKind::Projection(pred) = clause.kind() {
                    let ty1 = self.project_bty(ty, pred.projection_ty.def_id)?;
                    let ty2 = pred.term;
                    self.subtyping(rcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }

    fn generic_arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        variance: Variance,
        arg1: &GenericArg,
        arg2: &GenericArg,
    ) -> Result {
        let (ty1, ty2) = match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => (ty1.clone(), ty2.clone()),
            (GenericArg::Base(ctor1), GenericArg::Base(ctor2)) => {
                debug_assert_eq!(ctor1.sort(), ctor2.sort());
                (ctor1.to_ty(), ctor2.to_ty())
            }
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => return Ok(()),
            (GenericArg::Const(c1), GenericArg::Const(c2)) => {
                debug_assert_eq!(c1, c2);
                return Ok(());
            }
            _ => {
                let note = format!("incompatible generic args: `{arg1:?}` `{arg2:?}`");
                return Err(QueryErr::bug(note).into());
            }
        };
        match variance {
            Variance::Covariant => self.subtyping(rcx, &ty1, &ty2),
            Variance::Invariant => {
                self.subtyping(rcx, &ty1, &ty2)?;
                self.subtyping(rcx, &ty2, &ty1)
            }
            Variance::Contravariant => self.subtyping(rcx, &ty2, &ty1),
            Variance::Bivariant => Ok(()),
        }
    }

    fn idx_eq(&mut self, rcx: &mut RefineCtxt, e1: &Expr, e2: &Expr) {
        if e1 == e2 {
            return;
        }

        match (e1.kind(), e2.kind()) {
            (ExprKind::Aggregate(kind1, flds1), ExprKind::Aggregate(kind2, flds2)) => {
                debug_assert_eq!(kind1, kind2);
                for (e1, e2) in iter::zip(flds1, flds2) {
                    self.idx_eq(rcx, e1, e2);
                }
            }
            (_, ExprKind::Aggregate(kind2, flds2)) => {
                for (f, e2) in flds2.iter().enumerate() {
                    let e1 = e1.proj_and_reduce(kind2.to_proj(f as u32));
                    self.idx_eq(rcx, &e1, e2);
                }
            }
            (ExprKind::Aggregate(kind1, flds1), _) => {
                self.unify_exprs(e1, e2);
                for (f, e1) in flds1.iter().enumerate() {
                    let e2 = e2.proj_and_reduce(kind1.to_proj(f as u32));
                    self.idx_eq(rcx, e1, &e2);
                }
            }
            (ExprKind::Abs(p1), ExprKind::Abs(p2)) => {
                self.abs_eq(rcx, p1, p2);
            }
            (_, ExprKind::Abs(p)) => {
                self.abs_eq(rcx, &e1.eta_expand_abs(&p.inputs(), p.output()), p);
            }
            (ExprKind::Abs(p), _) => {
                self.unify_exprs(e1, e2);
                self.abs_eq(rcx, p, &e2.eta_expand_abs(&p.inputs(), p.output()));
            }
            (ExprKind::KVar(_), _) | (_, ExprKind::KVar(_)) => {
                rcx.check_impl(e1, e2, self.tag);
                rcx.check_impl(e2, e1, self.tag);
            }
            _ => {
                self.unify_exprs(e1, e2);
                let span = e2.span();
                rcx.check_pred(Expr::eq_at(e1, e2, span), self.tag);
            }
        }
    }

    fn abs_eq(&mut self, rcx: &mut RefineCtxt, f1: &Lambda, f2: &Lambda) {
        debug_assert_eq!(f1.inputs(), f2.inputs());
        let vars = f1.inputs().iter().map(|s| rcx.define_vars(s)).collect_vec();
        let e1 = f1.apply(&vars);
        let e2 = f2.apply(&vars);
        self.idx_eq(rcx, &e1, &e2);
    }

    fn unify_exprs(&self, e1: &Expr, e2: &Expr) {
        let mut evar_gen = self.evar_gen.borrow_mut();
        if let ExprKind::Var(Var::EVar(evar)) = e2.kind()
            && let scope = &evar_gen.data(evar.cx())
            && !scope.has_free_vars(e1)
        {
            evar_gen.unify(*evar, e1, false);
        }
    }

    pub(crate) fn solve(self) -> Result<EVarSol> {
        let mut evar_gen = self.evar_gen.into_inner();
        evar_gen.exit_context();
        Ok(evar_gen.try_solve_pending()?)
    }
}

impl Obligations {
    fn new(predicates: List<rty::Clause>, snapshot: Snapshot) -> Self {
        Self { predicates, snapshot }
    }
}

fn mk_generator_obligations(
    genv: GlobalEnv,
    generator_did: &DefId,
    resume_ty: &Ty,
    upvar_tys: &List<Ty>,
    opaque_def_id: &DefId,
) -> Result<Vec<rty::Clause>> {
    let bounds = genv.item_bounds(*opaque_def_id)?.skip_binder();
    for bound in &bounds {
        if let rty::ClauseKind::Projection(proj) = bound.kind() {
            let output = proj.term;
            let pred = CoroutineObligPredicate {
                def_id: *generator_did,
                resume_ty: resume_ty.clone(),
                upvar_tys: upvar_tys.clone(),
                output,
            };
            let clause = rty::Clause::new(vec![], rty::ClauseKind::CoroutineOblig(pred));
            return Ok(vec![clause]);
        }
    }
    bug!("no projection predicate")
}

fn mk_obligations(
    genv: GlobalEnv,
    did: DefId,
    args: &[GenericArg],
    refine_args: &[Expr],
) -> Result<List<rty::Clause>> {
    let tcx = genv.tcx();
    Ok(genv
        .predicates_of(did)?
        .predicates()
        .instantiate(tcx, args, refine_args))
}

impl<F> KVarGen for F
where
    F: Fn(&[List<Sort>], KVarEncoding) -> Expr,
{
    fn fresh(&self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr {
        (self)(binders, kind)
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;

    use super::*;

    impl Pretty for Tag {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} at {:?}", ^self.reason, self.src_span)
        }
    }

    impl_debug_with_default_cx!(Tag);
}
