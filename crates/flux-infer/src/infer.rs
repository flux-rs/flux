use std::{cell::RefCell, iter};

use flux_common::bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    queries::QueryErr,
    rty::{
        self,
        evars::{EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        AliasTy, BaseTy, CoroutineObligPredicate, ESpan, EVarGen, EarlyBinder, Expr, ExprKind,
        GenericArg, HoleKind, InferMode, Lambda, Mutability, PolyVariant, Sort, Ty, TyKind, Var,
    },
    rustc::mir::BasicBlock,
};
use itertools::{izip, Itertools};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::{BoundRegionConversionTime, RegionVariableOrigin};
use rustc_middle::ty::{BoundRegionKind, Variance};
use rustc_span::Span;

use crate::{
    fixpoint_encoding::KVarEncoding,
    refine_tree::{RefineCtxt, Scope},
};

pub type InferResult<T = ()> = std::result::Result<T, InferErr>;

pub trait KVarGen {
    fn fresh(&self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr;
}

pub struct InferCtxt<'a, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    pub def_id: DefId,
    pub refparams: &'a [Expr],
    kvar_gen: Box<(dyn KVarGen + 'a)>,
    evar_gen: RefCell<EVarGen<Scope>>,
    /// The span at which this inference context was created in `Checker`
    span: Span,
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

impl<'a, 'genv, 'tcx> InferCtxt<'a, 'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'a [Expr],
        kvar_gen: impl KVarGen + 'a,
        span: Span,
    ) -> Self {
        Self {
            genv,
            region_infcx,
            def_id,
            refparams,
            kvar_gen: Box::new(kvar_gen),
            evar_gen: RefCell::new(EVarGen::default()),
            span,
        }
    }

    pub fn at(&mut self, reason: ConstrReason) -> InferCtxtAt<'_, 'a, 'genv, 'tcx> {
        InferCtxtAt { infcx: self, reason }
    }

    pub fn instantiate_refine_args(&mut self, callee_def_id: DefId) -> InferResult<Vec<Expr>> {
        Ok(self
            .genv
            .refinement_generics_of(callee_def_id)?
            .collect_all_params(self.genv, |param| self.fresh_infer_var(&param.sort, param.mode))?)
    }

    pub fn instantiate_generic_args(&mut self, args: &[GenericArg]) -> Vec<GenericArg> {
        args.iter()
            .map(|a| a.replace_holes(|binders, kind| self.fresh_infer_var_for_hole(binders, kind)))
            .collect_vec()
    }

    fn next_region_var(&self, origin: RegionVariableOrigin) -> rty::Region {
        rty::ReVar(self.region_infcx.next_region_var(origin).as_var())
    }

    pub fn next_bound_region_var(
        &self,
        span: Span,
        kind: BoundRegionKind,
        conversion_time: BoundRegionConversionTime,
    ) -> rty::Region {
        self.next_region_var(RegionVariableOrigin::BoundRegion(span, kind, conversion_time))
    }

    pub fn fresh_infer_var(&self, sort: &Sort, mode: InferMode) -> Expr {
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

    pub fn fresh_infer_var_for_hole(&mut self, binders: &[List<Sort>], kind: HoleKind) -> Expr {
        match kind {
            HoleKind::Pred => self.fresh_kvar(binders, KVarEncoding::Conj),
            HoleKind::Expr(sort) => {
                assert!(binders.is_empty(), "TODO: implement evars under binders");
                self.fresh_evars(&sort)
            }
        }
    }

    pub fn fresh_kvar(&self, sorts: &[List<Sort>], encoding: KVarEncoding) -> Expr {
        self.kvar_gen.fresh(sorts, encoding)
    }

    fn fresh_evars(&self, sort: &Sort) -> Expr {
        let mut evar_gen = self.evar_gen.borrow_mut();
        Expr::fold_sort(sort, |_| Expr::evar(evar_gen.fresh_in_current()))
    }

    pub fn unify_exprs(&self, e1: &Expr, e2: &Expr) {
        let mut evar_gen = self.evar_gen.borrow_mut();
        if let ExprKind::Var(Var::EVar(evar)) = e2.kind()
            && let scope = &evar_gen.data(evar.cx())
            && !scope.has_free_vars(e1)
        {
            evar_gen.unify(*evar, e1, false);
        }
    }

    pub fn push_scope(&mut self, rcx: &RefineCtxt) {
        self.evar_gen.borrow_mut().enter_context(rcx.scope());
    }

    pub fn pop_scope(&mut self) -> InferResult<EVarSol> {
        let mut evar_gen = self.evar_gen.borrow_mut();
        evar_gen.exit_context();
        Ok(evar_gen.try_solve_pending()?)
    }

    fn pop_scope_without_solving_evars(&mut self) {
        self.evar_gen.borrow_mut().exit_context();
    }
}

pub struct InferCtxtAt<'a, 'b, 'genv, 'tcx> {
    pub infcx: &'a mut InferCtxt<'b, 'genv, 'tcx>,
    pub reason: ConstrReason,
}

impl<'a, 'b, 'genv, 'tcx> InferCtxtAt<'a, 'b, 'genv, 'tcx> {
    fn tag(&self) -> Tag {
        Tag::new(self.reason, self.infcx.span)
    }

    pub fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>) {
        rcx.check_pred(pred, self.tag());
    }

    pub fn check_non_closure_clauses(
        &mut self,
        rcx: &mut RefineCtxt,
        clauses: &[rty::Clause],
    ) -> InferResult {
        for clause in clauses {
            if let rty::ClauseKind::Projection(projection_pred) = clause.kind() {
                let impl_elem = Ty::projection(projection_pred.projection_ty)
                    .normalize_projections(
                        self.infcx.genv,
                        self.infcx.region_infcx,
                        self.infcx.def_id,
                        self.infcx.refparams,
                    )?;
                let term = projection_pred.term.normalize_projections(
                    self.infcx.genv,
                    self.infcx.region_infcx,
                    self.infcx.def_id,
                    self.infcx.refparams,
                )?;

                // TODO: does this really need to be invariant? https://github.com/flux-rs/flux/pull/478#issuecomment-1654035374
                self.subtyping(rcx, &impl_elem, &term)?;
                self.subtyping(rcx, &term, &impl_elem)?;
            }
        }
        Ok(())
    }

    /// Relate types via subtyping and returns coroutine obligations. See comment for
    /// [`Sub::obligations`].
    pub fn subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty1: &Ty,
        ty2: &Ty,
    ) -> InferResult<Vec<rty::Clause>> {
        let mut sub = Sub { infcx: self.infcx, reason: self.reason, obligations: vec![] };
        sub.tys(rcx, ty1, ty2)?;
        Ok(sub.obligations)
    }

    // FIXME(nilehmann) this is similar to `Checker::check_call`, but since is used from
    // `place_ty::fold` we cannot use that directly. We should try to unify them, because
    // there are a couple of things missing here (e.g., checking clauses on the struct definition).
    pub fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: EarlyBinder<PolyVariant>,
        generic_args: &[GenericArg],
        fields: &[Ty],
    ) -> InferResult<Ty> {
        self.infcx.push_scope(rcx);
        let tcx = self.infcx.genv.tcx();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = self.infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(tcx, &generic_args, &[])
            .replace_bound_refts_with(|sort, mode, _| self.infcx.fresh_infer_var(sort, mode));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            self.subtyping(rcx, actual, formal)?;
        }

        // Replace evars
        let evars_sol = self.infcx.pop_scope()?;
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret().replace_evars(&evars_sol))
    }
}

/// Context to relate two types `a` and `b` via subtyping
struct Sub<'a, 'b, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'b, 'genv, 'tcx>,
    reason: ConstrReason,
    /// FIXME(nilehmann) This is used to store coroutine obligations generated during subtyping when
    /// relating an opaque type. Other obligations related to relating opaque types are resolved
    /// directly here. The implementation is a really messy and we may be missing some obligations.
    /// We should revisit at some point.
    obligations: Vec<rty::Clause>,
}

impl<'a, 'b, 'genv, 'tcx> Sub<'a, 'b, 'genv, 'tcx> {
    fn tag(&self) -> Tag {
        Tag::new(self.reason, self.infcx.span)
    }

    fn tys(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) -> InferResult {
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
                self.infcx.push_scope(rcx);
                let ty2 = ty2.replace_bound_refts_with(|sort, mode, _| {
                    self.infcx.fresh_infer_var(sort, mode)
                });
                self.tys(rcx, &ty1, &ty2)?;
                self.infcx.pop_scope_without_solving_evars();
                Ok(())
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.btys(rcx, bty1, bty2)?;
                self.idxs_eq(rcx, idx1, idx2);
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
            (_, TyKind::Uninit) => Ok(()),
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2, self.tag());
                self.tys(rcx, &ty1, ty2)
            }
            (TyKind::Downcast(.., fields1), TyKind::Downcast(.., fields2)) => {
                debug_assert_eq!(fields1.len(), fields2.len());
                for (field1, field2) in iter::zip(fields1, fields2) {
                    self.tys(rcx, field1, field2)?;
                }
                Ok(())
            }
            (_, TyKind::Alias(rty::AliasKind::Opaque, alias_ty)) => {
                if let TyKind::Alias(rty::AliasKind::Opaque, alias_ty1) = ty1.kind() {
                    debug_assert_eq!(alias_ty1.refine_args.len(), alias_ty.refine_args.len());
                    iter::zip(alias_ty1.refine_args.iter(), alias_ty.refine_args.iter())
                        .for_each(|(e1, e2)| self.infcx.unify_exprs(e1, e2));
                }

                self.handle_opaque_type(rcx, &ty1, alias_ty)
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

    fn btys(&mut self, rcx: &mut RefineCtxt, bty1: &BaseTy, bty2: &BaseTy) -> InferResult {
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
                let variances = self.infcx.genv.variances_of(adt1.did());
                for (variance, ty1, ty2) in izip!(variances, args1.iter(), args2.iter()) {
                    self.generic_args(rcx, *variance, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ok(())
            }

            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => self.tys(rcx, ty1, ty2),
            (BaseTy::Ref(_, ty1, Mutability::Mut), BaseTy::Ref(_, ty2, Mutability::Mut)) => {
                self.tys(rcx, ty1, ty2)?;
                self.tys(rcx, ty2, ty1)
            }
            (BaseTy::Ref(_, ty1, Mutability::Not), BaseTy::Ref(_, ty2, Mutability::Not)) => {
                self.tys(rcx, ty1, ty2)
            }
            (BaseTy::Tuple(tys1), BaseTy::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.tys(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1, len2);
                self.tys(rcx, ty1, ty2)
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
                    self.tys(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            _ => Err(QueryErr::bug(format!("incompatible base types: `{bty1:?}` - `{bty2:?}`")))?,
        }
    }

    fn generic_args(
        &mut self,
        rcx: &mut RefineCtxt,
        variance: Variance,
        arg1: &GenericArg,
        arg2: &GenericArg,
    ) -> InferResult {
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
            Variance::Covariant => self.tys(rcx, &ty1, &ty2),
            Variance::Invariant => {
                self.tys(rcx, &ty1, &ty2)?;
                self.tys(rcx, &ty2, &ty1)
            }
            Variance::Contravariant => self.tys(rcx, &ty2, &ty1),
            Variance::Bivariant => Ok(()),
        }
    }

    fn idxs_eq(&mut self, rcx: &mut RefineCtxt, e1: &Expr, e2: &Expr) {
        if e1 == e2 {
            return;
        }

        match (e1.kind(), e2.kind()) {
            (ExprKind::Aggregate(kind1, flds1), ExprKind::Aggregate(kind2, flds2)) => {
                debug_assert_eq!(kind1, kind2);
                for (e1, e2) in iter::zip(flds1, flds2) {
                    self.idxs_eq(rcx, e1, e2);
                }
            }
            (_, ExprKind::Aggregate(kind2, flds2)) => {
                for (f, e2) in flds2.iter().enumerate() {
                    let e1 = e1.proj_and_reduce(kind2.to_proj(f as u32));
                    self.idxs_eq(rcx, &e1, e2);
                }
            }
            (ExprKind::Aggregate(kind1, flds1), _) => {
                self.infcx.unify_exprs(e1, e2);
                for (f, e1) in flds1.iter().enumerate() {
                    let e2 = e2.proj_and_reduce(kind1.to_proj(f as u32));
                    self.idxs_eq(rcx, e1, &e2);
                }
            }
            (ExprKind::Abs(p1), ExprKind::Abs(p2)) => {
                self.abs_eq(rcx, p1, p2);
            }
            (_, ExprKind::Abs(p)) => {
                self.abs_eq(rcx, &e1.eta_expand_abs(&p.inputs(), p.output()), p);
            }
            (ExprKind::Abs(p), _) => {
                self.infcx.unify_exprs(e1, e2);
                self.abs_eq(rcx, p, &e2.eta_expand_abs(&p.inputs(), p.output()));
            }
            (ExprKind::KVar(_), _) | (_, ExprKind::KVar(_)) => {
                rcx.check_impl(e1, e2, self.tag());
                rcx.check_impl(e2, e1, self.tag());
            }
            _ => {
                self.infcx.unify_exprs(e1, e2);
                let span = e2.span();
                rcx.check_pred(Expr::eq_at(e1, e2, span), self.tag());
            }
        }
    }

    fn abs_eq(&mut self, rcx: &mut RefineCtxt, f1: &Lambda, f2: &Lambda) {
        debug_assert_eq!(f1.inputs(), f2.inputs());
        let vars = f1.inputs().iter().map(|s| rcx.define_vars(s)).collect_vec();
        let e1 = f1.apply(&vars);
        let e2 = f2.apply(&vars);
        self.idxs_eq(rcx, &e1, &e2);
    }

    fn handle_opaque_type(
        &mut self,
        rcx: &mut RefineCtxt,
        ty: &Ty,
        alias_ty: &AliasTy,
    ) -> InferResult {
        if let Some(BaseTy::Coroutine(def_id, resume_ty, upvar_tys)) =
            ty.as_bty_skipping_existentials()
        {
            let obligs = mk_coroutine_obligations(
                self.infcx.genv,
                def_id,
                resume_ty,
                upvar_tys,
                &alias_ty.def_id,
            )?;
            self.obligations.extend(obligs);
        } else {
            let bounds = self
                .infcx
                .genv
                .item_bounds(alias_ty.def_id)?
                .instantiate_identity(self.infcx.refparams);
            for clause in &bounds {
                if let rty::ClauseKind::Projection(pred) = clause.kind() {
                    let ty1 = self.project_bty(ty, pred.projection_ty.def_id)?;
                    let ty2 = pred.term;
                    self.tys(rcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }

    fn project_bty(&mut self, self_ty: &Ty, def_id: DefId) -> InferResult<Ty> {
        let args = List::singleton(GenericArg::Ty(self_ty.clone()));
        let alias_ty = rty::AliasTy::new(def_id, args, List::empty());
        Ok(Ty::projection(alias_ty).normalize_projections(
            self.infcx.genv,
            self.infcx.region_infcx,
            self.infcx.def_id,
            self.infcx.refparams,
        )?)
    }
}

fn mk_coroutine_obligations(
    genv: GlobalEnv,
    generator_did: &DefId,
    resume_ty: &Ty,
    upvar_tys: &List<Ty>,
    opaque_def_id: &DefId,
) -> InferResult<Vec<rty::Clause>> {
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

#[derive(Debug)]
pub enum InferErr {
    Inference,
    Query(QueryErr),
}

impl From<UnsolvedEvar> for InferErr {
    fn from(_: UnsolvedEvar) -> Self {
        InferErr::Inference
    }
}

impl From<QueryErr> for InferErr {
    fn from(v: QueryErr) -> Self {
        Self::Query(v)
    }
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
