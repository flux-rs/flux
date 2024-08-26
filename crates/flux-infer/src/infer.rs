use std::{cell::RefCell, fmt, iter};

use flux_common::bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    queries::{QueryErr, QueryResult},
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
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::infer::{BoundRegionConversionTime, RegionVariableOrigin};
use rustc_middle::ty::{BoundRegionKind, Variance};
use rustc_span::Span;

use crate::{
    fixpoint_encoding::{KVarEncoding, KVarGen},
    refine_tree::{RefineCtxt, RefineTree, Scope, Snapshot},
};

pub type InferResult<T = ()> = std::result::Result<T, InferErr>;

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

pub struct InferCtxtRoot<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    inner: RefCell<InferCtxtInner>,
    refine_tree: RefineTree,
    root: Snapshot,
    refine_params: List<Expr>,
}

impl<'genv, 'tcx> InferCtxtRoot<'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        root_id: LocalDefId,
        kvar_gen: KVarGen,
    ) -> QueryResult<Self> {
        let generics = genv.generics_of(root_id)?;
        let const_params = generics.const_params(genv)?;
        let mut refine_tree = RefineTree::new(const_params);

        let mut rcx = refine_tree.refine_ctxt_at_root();
        let refine_params = genv
            .refinement_generics_of(root_id)?
            .collect_all_params(genv, |param| rcx.define_vars(&param.sort))?;
        let root = rcx.snapshot();

        Ok(Self {
            genv,
            inner: RefCell::new(InferCtxtInner::new(kvar_gen)),
            refine_tree,
            root,
            refine_params,
        })
    }

    pub fn infcx<'a>(
        &'a mut self,
        def_id: LocalDefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt::new(
            self.genv,
            region_infcx,
            def_id.to_def_id(),
            &self.refine_params,
            self.refine_tree.refine_ctxt_at(&self.root).unwrap(),
            &self.inner,
        )
    }

    pub fn split(self) -> (RefineTree, KVarGen) {
        (self.refine_tree, self.inner.into_inner().kvars)
    }
}

pub struct InferCtxt<'infcx, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub region_infcx: &'infcx rustc_infer::infer::InferCtxt<'tcx>,
    pub def_id: DefId,
    pub refparams: &'infcx [Expr],
    rcx: RefineCtxt<'infcx>,
    inner: &'infcx RefCell<InferCtxtInner>,
}

struct InferCtxtInner {
    kvars: KVarGen,
    evars: EVarGen<Scope>,
}

impl InferCtxtInner {
    fn new(kvars: KVarGen) -> Self {
        Self { kvars, evars: Default::default() }
    }
}

impl<'infcx, 'genv, 'tcx> InferCtxt<'infcx, 'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        region_infcx: &'infcx rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'infcx [Expr],
        rcx: RefineCtxt<'infcx>,
        inner: &'infcx RefCell<InferCtxtInner>,
    ) -> Self {
        Self { genv, region_infcx, def_id, refparams, rcx, inner }
    }

    pub fn clean_subtree(&mut self, snapshot: &Snapshot) {
        self.rcx.clear_children(snapshot);
    }

    pub fn change_item<'a>(
        &'a mut self,
        def_id: LocalDefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        snapshot: &Snapshot,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt {
            def_id: def_id.to_def_id(),
            rcx: self.rcx.change_root(snapshot).unwrap(),
            region_infcx,
            ..*self
        }
    }

    pub fn change_root(&mut self, snapshot: &Snapshot) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt { rcx: self.rcx.change_root(snapshot).unwrap(), ..*self }
    }

    pub fn branch(&mut self) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt { rcx: self.rcx.branch(), ..*self }
    }

    pub fn at(&mut self, span: Span) -> InferCtxtAt<'_, 'infcx, 'genv, 'tcx> {
        InferCtxtAt { infcx: self, span }
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

    /// Generate a fresh kvar in the current scope. See [`KVarGen::fresh`].
    pub fn fresh_kvar(&self, sorts: &[List<Sort>], encoding: KVarEncoding) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner
            .kvars
            .fresh(sorts, inner.evars.current_data().iter(), encoding)
    }

    fn fresh_evars(&self, sort: &Sort) -> Expr {
        let evars = &mut self.inner.borrow_mut().evars;
        Expr::fold_sort(sort, |_| Expr::evar(evars.fresh_in_current()))
    }

    pub fn unify_exprs(&self, e1: &Expr, e2: &Expr) {
        let evars = &mut self.inner.borrow_mut().evars;
        if let ExprKind::Var(Var::EVar(evar)) = e2.kind()
            && let scope = &evars.data(evar.cx())
            && !scope.has_free_vars(e1)
        {
            evars.unify(*evar, e1, false);
        }
    }

    pub fn push_scope(&mut self) {
        let scope = self.scope();
        self.inner.borrow_mut().evars.enter_context(scope);
    }

    pub fn pop_scope(&mut self) -> InferResult<EVarSol> {
        let evars = &mut self.inner.borrow_mut().evars;
        evars.exit_context();
        Ok(evars.try_solve_pending()?)
    }

    fn pop_scope_without_solving_evars(&mut self) {
        self.inner.borrow_mut().evars.exit_context();
    }
}

impl std::fmt::Debug for InferCtxt<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.rcx, f)
    }
}

impl<'infcx> std::ops::Deref for InferCtxt<'infcx, '_, '_> {
    type Target = RefineCtxt<'infcx>;

    fn deref(&self) -> &Self::Target {
        &self.rcx
    }
}

impl std::ops::DerefMut for InferCtxt<'_, '_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.rcx
    }
}

pub struct InferCtxtAt<'a, 'infcx, 'genv, 'tcx> {
    pub infcx: &'a mut InferCtxt<'infcx, 'genv, 'tcx>,
    pub span: Span,
}

impl<'a, 'infcx, 'genv, 'tcx> InferCtxtAt<'a, 'infcx, 'genv, 'tcx> {
    fn tag(&self, reason: ConstrReason) -> Tag {
        Tag::new(reason, self.span)
    }
    pub fn check_pred(&mut self, pred: impl Into<Expr>, reason: ConstrReason) {
        let tag = self.tag(reason);
        self.infcx.check_pred(pred, tag);
    }

    pub fn check_non_closure_clauses(
        &mut self,
        clauses: &[rty::Clause],
        reason: ConstrReason,
    ) -> InferResult {
        for clause in clauses {
            if let rty::ClauseKind::Projection(projection_pred) = clause.kind_skipping_binder() {
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
                self.subtyping(&impl_elem, &term, reason)?;
                self.subtyping(&term, &impl_elem, reason)?;
            }
        }
        Ok(())
    }

    /// Relate types via subtyping and returns coroutine obligations. See comment for
    /// [`Sub::obligations`].
    pub fn subtyping(
        &mut self,
        ty1: &Ty,
        ty2: &Ty,
        reason: ConstrReason,
    ) -> InferResult<Vec<rty::Clause>> {
        let mut sub = Sub { span: self.span, reason, obligations: vec![] };
        sub.tys(self.infcx, ty1, ty2)?;
        Ok(sub.obligations)
    }

    // FIXME(nilehmann) this is similar to `Checker::check_call`, but since is used from
    // `place_ty::fold` we cannot use that directly. We should try to unify them, because
    // there are a couple of things missing here (e.g., checking clauses on the struct definition).
    pub fn check_constructor(
        &mut self,
        variant: EarlyBinder<PolyVariant>,
        generic_args: &[GenericArg],
        fields: &[Ty],
        reason: ConstrReason,
    ) -> InferResult<Ty> {
        self.infcx.push_scope();
        let tcx = self.infcx.genv.tcx();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = self.infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(tcx, &generic_args, &[])
            .replace_bound_refts_with(|sort, mode, _| self.infcx.fresh_infer_var(sort, mode));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            self.subtyping(actual, formal, reason)?;
        }

        // Replace evars
        let evars_sol = self.infcx.pop_scope()?;
        self.infcx.replace_evars(&evars_sol);

        Ok(variant.ret().replace_evars(&evars_sol))
    }
}

impl<'a, 'genv, 'tcx> std::ops::Deref for InferCtxtAt<'_, 'a, 'genv, 'tcx> {
    type Target = InferCtxt<'a, 'genv, 'tcx>;

    fn deref(&self) -> &Self::Target {
        self.infcx
    }
}

impl std::ops::DerefMut for InferCtxtAt<'_, '_, '_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.infcx
    }
}

/// Used for debugging to attach a "trace" to the [`RefineTree`] that can be used to print information
/// to recover the derivation when relating types via subtyping. The code that attaches the trace is
/// currently commented out because the output is too verbose.
#[allow(dead_code)]
pub(crate) enum TypeTrace {
    Types(Ty, Ty),
    BaseTys(BaseTy, BaseTy),
}

#[allow(dead_code)]
impl TypeTrace {
    fn tys(a: &Ty, b: &Ty) -> Self {
        Self::Types(a.clone(), b.clone())
    }

    fn btys(a: &BaseTy, b: &BaseTy) -> Self {
        Self::BaseTys(a.clone(), b.clone())
    }

    pub(crate) fn replace_evars(&mut self, evars: &EVarSol) {
        match self {
            TypeTrace::Types(a, b) => {
                *self = TypeTrace::Types(a.replace_evars(evars), b.replace_evars(evars));
            }
            TypeTrace::BaseTys(a, b) => {
                *self = TypeTrace::BaseTys(a.replace_evars(evars), b.replace_evars(evars));
            }
        }
    }
}

impl fmt::Debug for TypeTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeTrace::Types(a, b) => write!(f, "{a:?} - {b:?}"),
            TypeTrace::BaseTys(a, b) => write!(f, "{a:?} - {b:?}"),
        }
    }
}

/// Context to relate two types `a` and `b` via subtyping
struct Sub {
    reason: ConstrReason,
    span: Span,
    /// FIXME(nilehmann) This is used to store coroutine obligations generated during subtyping when
    /// relating an opaque type. Other obligations related to relating opaque types are resolved
    /// directly here. The implementation is a really messy and we may be missing some obligations.
    /// We should revisit at some point.
    obligations: Vec<rty::Clause>,
}

impl Sub {
    fn tag(&self) -> Tag {
        Tag::new(self.reason, self.span)
    }

    fn tys(&mut self, infcx: &mut InferCtxt, a: &Ty, b: &Ty) -> InferResult {
        let infcx = &mut infcx.branch();

        // infcx.push_trace(TypeTrace::tys(a, b));

        // We *fully* unpack the lhs before continuing to be able to prove goals like this
        // ∃a. (i32[a], ∃b. {i32[b] | a > b})} <: ∃a,b. ({i32[a] | b < a}, i32[b])
        // See S4.5 in https://arxiv.org/pdf/2209.13000v1.pdf
        let a = infcx.unpack(a);

        match (a.kind(), b.kind()) {
            (TyKind::Exists(..), _) => {
                bug!("existentials should be removed by the unpack");
            }
            (TyKind::Constr(..), _) => {
                bug!("constraint types should removed by the unpack");
            }
            (_, TyKind::Exists(ty_b)) => {
                infcx.push_scope();
                let ty_b = ty_b
                    .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));
                self.tys(infcx, &a, &ty_b)?;
                infcx.pop_scope_without_solving_evars();
                Ok(())
            }
            (TyKind::Indexed(bty_a, idx_a), TyKind::Indexed(bty_b, idx_b)) => {
                self.btys(infcx, bty_a, bty_b)?;
                self.idxs_eq(infcx, idx_a, idx_b);
                Ok(())
            }
            (TyKind::Ptr(pk_a, path_a), TyKind::Ptr(pk_b, path_b)) => {
                debug_assert_eq!(pk_a, pk_b);
                debug_assert_eq!(path_a, path_b);
                Ok(())
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ok(())
            }
            (_, TyKind::Uninit) => Ok(()),
            (_, TyKind::Constr(pred_b, ty_b)) => {
                infcx.check_pred(pred_b, self.tag());
                self.tys(infcx, &a, ty_b)
            }
            (TyKind::Downcast(.., fields_a), TyKind::Downcast(.., fields_b)) => {
                debug_assert_eq!(fields_a.len(), fields_b.len());
                for (ty_a, ty_b) in iter::zip(fields_a, fields_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            (_, TyKind::Alias(rty::AliasKind::Opaque, alias_ty_b)) => {
                if let TyKind::Alias(rty::AliasKind::Opaque, alias_ty_a) = a.kind() {
                    debug_assert_eq!(alias_ty_a.refine_args.len(), alias_ty_b.refine_args.len());
                    iter::zip(alias_ty_a.refine_args.iter(), alias_ty_b.refine_args.iter())
                        .for_each(|(expr_a, expr_b)| infcx.unify_exprs(expr_a, expr_b));
                }

                self.handle_opaque_type(infcx, &a, alias_ty_b)
            }
            (
                TyKind::Alias(rty::AliasKind::Projection, alias_ty_a),
                TyKind::Alias(rty::AliasKind::Projection, alias_ty_b),
            ) => {
                debug_assert_eq!(alias_ty_a, alias_ty_b);
                Ok(())
            }
            _ => Err(QueryErr::bug(format!("incompatible types: `{a:?}` - `{b:?}`")))?,
        }
    }

    fn btys(&mut self, infcx: &mut InferCtxt, a: &BaseTy, b: &BaseTy) -> InferResult {
        // infcx.push_trace(TypeTrace::btys(a, b));

        match (a, b) {
            (BaseTy::Int(int_ty_a), BaseTy::Int(int_ty_b)) => {
                debug_assert_eq!(int_ty_a, int_ty_b);
                Ok(())
            }
            (BaseTy::Uint(uint_ty_a), BaseTy::Uint(uint_ty_b)) => {
                debug_assert_eq!(uint_ty_a, uint_ty_b);
                Ok(())
            }
            (BaseTy::Adt(adt_a, args_a), BaseTy::Adt(adt_b, args_b)) => {
                debug_assert_eq!(adt_a.did(), adt_b.did());
                debug_assert_eq!(args_a.len(), args_b.len());
                let variances = infcx.genv.variances_of(adt_a.did());
                for (variance, ty_a, ty_b) in izip!(variances, args_a.iter(), args_b.iter()) {
                    self.generic_args(infcx, *variance, ty_a, ty_b)?;
                }
                Ok(())
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ok(())
            }

            (BaseTy::Slice(ty_a), BaseTy::Slice(ty_b)) => self.tys(infcx, ty_a, ty_b),
            (BaseTy::Ref(_, ty_a, Mutability::Mut), BaseTy::Ref(_, ty_b, Mutability::Mut)) => {
                self.tys(infcx, ty_a, ty_b)?;
                self.tys(infcx, ty_b, ty_a)
            }
            (BaseTy::Ref(_, ty_a, Mutability::Not), BaseTy::Ref(_, ty_b, Mutability::Not)) => {
                self.tys(infcx, ty_a, ty_b)
            }
            (BaseTy::Tuple(tys_a), BaseTy::Tuple(tys_b)) => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            (BaseTy::Array(ty_a, len_a), BaseTy::Array(ty_b, len_b)) => {
                debug_assert_eq!(len_a, len_b);
                self.tys(infcx, ty_a, ty_b)
            }
            (BaseTy::Param(param_a), BaseTy::Param(param_b)) => {
                debug_assert_eq!(param_a, param_b);
                Ok(())
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtr(_, _), BaseTy::RawPtr(_, _)) => Ok(()),
            (BaseTy::Dynamic(preds_a, _), BaseTy::Dynamic(preds_b, _)) => {
                assert_eq!(preds_a, preds_b);
                Ok(())
            }
            (BaseTy::Closure(did1, tys_a), BaseTy::Closure(did2, tys_b)) if did1 == did2 => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            _ => Err(QueryErr::bug(format!("incompatible base types: `{a:?}` - `{b:?}`")))?,
        }
    }

    fn generic_args(
        &mut self,
        infcx: &mut InferCtxt,
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
            Variance::Covariant => self.tys(infcx, &ty1, &ty2),
            Variance::Invariant => {
                self.tys(infcx, &ty1, &ty2)?;
                self.tys(infcx, &ty2, &ty1)
            }
            Variance::Contravariant => self.tys(infcx, &ty2, &ty1),
            Variance::Bivariant => Ok(()),
        }
    }

    fn idxs_eq(&mut self, infcx: &mut InferCtxt, e1: &Expr, e2: &Expr) {
        if e1 == e2 {
            return;
        }

        match (e1.kind(), e2.kind()) {
            (ExprKind::Aggregate(kind1, flds1), ExprKind::Aggregate(kind2, flds2)) => {
                debug_assert_eq!(kind1, kind2);
                for (e1, e2) in iter::zip(flds1, flds2) {
                    self.idxs_eq(infcx, e1, e2);
                }
            }
            (_, ExprKind::Aggregate(kind2, flds2)) => {
                for (f, e2) in flds2.iter().enumerate() {
                    let e1 = e1.proj_and_reduce(kind2.to_proj(f as u32));
                    self.idxs_eq(infcx, &e1, e2);
                }
            }
            (ExprKind::Aggregate(kind1, flds1), _) => {
                infcx.unify_exprs(e1, e2);
                for (f, e1) in flds1.iter().enumerate() {
                    let e2 = e2.proj_and_reduce(kind1.to_proj(f as u32));
                    self.idxs_eq(infcx, e1, &e2);
                }
            }
            (ExprKind::Abs(p1), ExprKind::Abs(p2)) => {
                self.abs_eq(infcx, p1, p2);
            }
            (_, ExprKind::Abs(p)) => {
                self.abs_eq(infcx, &e1.eta_expand_abs(&p.inputs(), p.output()), p);
            }
            (ExprKind::Abs(p), _) => {
                infcx.unify_exprs(e1, e2);
                self.abs_eq(infcx, p, &e2.eta_expand_abs(&p.inputs(), p.output()));
            }
            (ExprKind::KVar(_), _) | (_, ExprKind::KVar(_)) => {
                infcx.check_impl(e1, e2, self.tag());
                infcx.check_impl(e2, e1, self.tag());
            }
            _ => {
                infcx.unify_exprs(e1, e2);
                let span = e2.span();
                infcx.check_pred(Expr::eq_at(e1, e2, span), self.tag());
            }
        }
    }

    fn abs_eq(&mut self, infcx: &mut InferCtxt, f1: &Lambda, f2: &Lambda) {
        debug_assert_eq!(f1.inputs(), f2.inputs());
        let vars = f1
            .inputs()
            .iter()
            .map(|s| infcx.define_vars(s))
            .collect_vec();
        let e1 = f1.apply(&vars);
        let e2 = f2.apply(&vars);
        self.idxs_eq(infcx, &e1, &e2);
    }

    fn handle_opaque_type(
        &mut self,
        infcx: &mut InferCtxt,
        ty: &Ty,
        alias_ty: &AliasTy,
    ) -> InferResult {
        if let Some(BaseTy::Coroutine(def_id, resume_ty, upvar_tys)) =
            ty.as_bty_skipping_existentials()
        {
            let obligs = mk_coroutine_obligations(
                infcx.genv,
                def_id,
                resume_ty,
                upvar_tys,
                &alias_ty.def_id,
            )?;
            self.obligations.extend(obligs);
        } else {
            let bounds = infcx
                .genv
                .item_bounds(alias_ty.def_id)?
                .instantiate_identity(infcx.refparams);
            for clause in &bounds {
                if let rty::ClauseKind::Projection(pred) = clause.kind_skipping_binder() {
                    let ty1 = Self::project_bty(infcx, ty, pred.projection_ty.def_id)?;
                    let ty2 = pred.term;
                    self.tys(infcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }

    fn project_bty(infcx: &InferCtxt, self_ty: &Ty, def_id: DefId) -> InferResult<Ty> {
        let args = List::singleton(GenericArg::Ty(self_ty.clone()));
        let alias_ty = rty::AliasTy::new(def_id, args, List::empty());
        Ok(Ty::projection(alias_ty).normalize_projections(
            infcx.genv,
            infcx.region_infcx,
            infcx.def_id,
            infcx.refparams,
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
        if let rty::ClauseKind::Projection(proj) = bound.kind_skipping_binder() {
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
