use std::{cell::RefCell, fmt, iter};

use flux_common::{bug, tracked_span_assert_eq, tracked_span_dbg_assert_eq};
use flux_middle::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self,
        evars::{EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        AliasKind, AliasTy, BaseTy, Binder, BoundVariableKinds, CoroutineObligPredicate, ESpan,
        EVar, EVarGen, EarlyBinder, Expr, ExprKind, GenericArg, GenericArgs, HoleKind, InferMode,
        Lambda, List, Loc, Mutability, Path, PolyVariant, PtrKind, Ref, Region, Sort, Ty, TyKind,
        Var,
    },
};
use itertools::{izip, Itertools};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::BasicBlock,
    ty::{TyCtxt, Variance},
};
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
    SubtypeIn,
    SubtypeReq,
    SubtypeOut,
    SubtypeEns,
}

pub struct InferCtxtRoot<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    inner: RefCell<InferCtxtInner>,
    refine_tree: RefineTree,
}

impl<'genv, 'tcx> InferCtxtRoot<'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        root_id: DefId,
        kvar_gen: KVarGen,
        args: Option<&GenericArgs>,
    ) -> QueryResult<Self> {
        Ok(Self {
            genv,
            inner: RefCell::new(InferCtxtInner::new(kvar_gen)),
            refine_tree: RefineTree::new(genv, root_id, args)?,
        })
    }

    pub fn infcx<'a>(
        &'a mut self,
        def_id: DefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt::new(
            self.genv,
            region_infcx,
            def_id,
            self.refine_tree.refine_ctxt_at_root(),
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
        rcx: RefineCtxt<'infcx>,
        inner: &'infcx RefCell<InferCtxtInner>,
    ) -> Self {
        Self { genv, region_infcx, def_id, rcx, inner }
    }

    pub fn clean_subtree(&mut self, snapshot: &Snapshot) {
        self.rcx.clear_children(snapshot);
    }

    pub fn change_item<'a>(
        &'a mut self,
        def_id: LocalDefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt { def_id: def_id.to_def_id(), rcx: self.rcx.branch(), region_infcx, ..*self }
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

    pub fn fresh_infer_var(&self, sort: &Sort, mode: InferMode) -> Expr {
        match mode {
            InferMode::KVar => {
                let fsort = sort.expect_func().expect_mono();
                let vars = fsort.inputs().iter().cloned().map_into().collect();
                let kvar = self.fresh_kvar(&[vars], KVarEncoding::Single);
                Expr::abs(Lambda::bind_with_fsort(kvar, fsort))
            }
            InferMode::EVar => self.fresh_evars(sort),
        }
    }

    pub fn fresh_infer_var_for_hole(
        &mut self,
        binders: &[BoundVariableKinds],
        kind: HoleKind,
    ) -> Expr {
        match kind {
            HoleKind::Pred => self.fresh_kvar(binders, KVarEncoding::Conj),
            HoleKind::Expr(sort) => {
                // We only use expression holes to infer early param arguments for opaque types
                // at function calls. These should be well-scoped in the current scope, so we ignore
                // the extra `binders` around the hole.
                self.fresh_evars(&sort)
            }
        }
    }

    /// Generate a fresh kvar in the current scope. See [`KVarGen::fresh`].
    pub fn fresh_kvar(&self, binders: &[BoundVariableKinds], encoding: KVarEncoding) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner
            .kvars
            .fresh(binders, inner.evars.current_data().iter(), encoding)
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

    fn enter_exists<T, U>(&mut self, exists: &Binder<T>, f: impl FnOnce(&mut Self, T) -> U) -> U
    where
        T: TypeFoldable,
    {
        self.push_scope();
        let t = exists.replace_bound_refts_with(|sort, mode, _| self.fresh_infer_var(sort, mode));
        let t = f(self, t);
        self.pop_scope_without_solving_evars();
        t
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

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.genv.tcx()
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
                let impl_elem = BaseTy::projection(projection_pred.projection_ty)
                    .to_ty()
                    .normalize_projections(
                        self.infcx.genv,
                        self.infcx.region_infcx,
                        self.infcx.def_id,
                    )?;
                let term = projection_pred.term.to_ty().normalize_projections(
                    self.infcx.genv,
                    self.infcx.region_infcx,
                    self.infcx.def_id,
                )?;

                // TODO: does this really need to be invariant? https://github.com/flux-rs/flux/pull/478#issuecomment-1654035374
                self.subtyping(&impl_elem, &term, reason)?;
                self.subtyping(&term, &impl_elem, reason)?;
            }
        }
        Ok(())
    }

    /// Relate types via subtyping for a function call. This is the same as [`InferCtxtAt::subtyping`]
    /// except that we also consider strong references.
    pub fn fun_arg_subtyping(
        &mut self,
        env: &mut impl LocEnv,
        a: &Ty,
        b: &Ty,
        reason: ConstrReason,
    ) -> InferResult {
        let mut sub = Sub::new(reason, self.span);
        sub.fun_args(self.infcx, env, a, b)
    }

    /// Relate types via subtyping and returns coroutine obligations. See comment for [`Sub::obligations`].
    pub fn subtyping(
        &mut self,
        a: &Ty,
        b: &Ty,
        reason: ConstrReason,
    ) -> InferResult<Vec<rty::Clause>> {
        let mut sub = Sub::new(reason, self.span);
        sub.tys(self.infcx, a, b)?;
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

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = self.infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(self.infcx.tcx(), &generic_args, &[])
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
pub(crate) enum TypeTrace {
    Types(Ty, Ty),
    BaseTys(BaseTy, BaseTy),
}

#[expect(dead_code, reason = "we use this for debugging some time")]
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

pub trait LocEnv {
    fn ptr_to_ref(
        &mut self,
        infcx: &mut InferCtxtAt,
        reason: ConstrReason,
        re: Region,
        path: &Path,
        bound: Ty,
    ) -> InferResult<Ty>;

    fn unfold_strg_ref(&mut self, infcx: &mut InferCtxt, path: &Path, ty: &Ty) -> InferResult<Loc>;
    fn get(&self, path: &Path) -> Ty;
}

/// Context used to relate two types `a` and `b` via subtyping
struct Sub {
    reason: ConstrReason,
    span: Span,
    /// FIXME(nilehmann) This is used to store coroutine obligations generated during subtyping when
    /// relating an opaque type. Other obligations related to relating opaque types are resolved
    /// directly here. The implementation is really messy and we may be missing some obligations.
    obligations: Vec<rty::Clause>,
}

impl Sub {
    fn new(reason: ConstrReason, span: Span) -> Self {
        Self { reason, span, obligations: vec![] }
    }

    fn tag(&self) -> Tag {
        Tag::new(self.reason, self.span)
    }

    fn fun_args(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut impl LocEnv,
        a: &Ty,
        b: &Ty,
    ) -> InferResult {
        let infcx = &mut infcx.branch();
        // infcx.push_trace(TypeTrace::tys(a, b));
        match (a.kind(), b.kind()) {
            (_, TyKind::Exists(ctor_b)) => {
                infcx.enter_exists(ctor_b, |infcx, ty_b| self.fun_args(infcx, env, a, &ty_b))
            }
            (_, TyKind::Constr(pred_b, ty_b)) => {
                infcx.check_pred(pred_b, self.tag());
                self.fun_args(infcx, env, a, ty_b)
            }
            (TyKind::Ptr(PtrKind::Mut(_), path1), TyKind::StrgRef(_, path2, ty2)) => {
                let ty1 = env.get(path1);
                infcx.unify_exprs(&path1.to_expr(), &path2.to_expr());
                self.tys(infcx, &ty1, ty2)
            }
            (TyKind::StrgRef(_, path1, ty1), TyKind::StrgRef(_, path2, ty2)) => {
                env.unfold_strg_ref(infcx, path1, ty1)?;
                let ty1 = env.get(path1);
                infcx.unify_exprs(&path1.to_expr(), &path2.to_expr());
                self.tys(infcx, &ty1, ty2)
            }
            (TyKind::Ptr(PtrKind::Mut(re), path), Ref!(_, bound, Mutability::Mut)) => {
                let mut at = infcx.at(self.span);
                env.ptr_to_ref(&mut at, ConstrReason::Call, *re, path, bound.clone())?;
                Ok(())
            }
            _ => self.tys(infcx, a, b),
        }
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
                bug!("existentials should be removed by the unpacking");
            }
            (TyKind::Constr(..), _) => {
                bug!("constraint types should removed by the unpacking");
            }
            (_, TyKind::Exists(ctor_b)) => {
                infcx.enter_exists(ctor_b, |infcx, ty_b| self.tys(infcx, &a, &ty_b))
            }
            (_, TyKind::Constr(pred_b, ty_b)) => {
                infcx.check_pred(pred_b, self.tag());
                self.tys(infcx, &a, ty_b)
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
            (TyKind::Downcast(.., fields_a), TyKind::Downcast(.., fields_b)) => {
                debug_assert_eq!(fields_a.len(), fields_b.len());
                for (ty_a, ty_b) in iter::zip(fields_a, fields_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            _ => Err(query_bug!("incompatible types: `{a:?}` - `{b:?}`"))?,
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
            (BaseTy::Adt(a_adt, a_args), BaseTy::Adt(b_adt, b_args)) => {
                tracked_span_dbg_assert_eq!(a_adt.did(), b_adt.did());
                tracked_span_dbg_assert_eq!(a_args.len(), b_args.len());
                let variances = infcx.genv.variances_of(a_adt.did());
                for (variance, ty_a, ty_b) in izip!(variances, a_args.iter(), b_args.iter()) {
                    self.generic_args(infcx, *variance, ty_a, ty_b)?;
                }
                Ok(())
            }
            (BaseTy::FnDef(a_def_id, a_args), BaseTy::FnDef(b_def_id, b_args)) => {
                debug_assert_eq!(a_def_id, b_def_id);
                debug_assert_eq!(a_args.len(), b_args.len());
                // NOTE: we don't check subtyping here because the RHS is *really*
                // the function type, the LHS is just generated by rustc.
                // we could generate a subtyping constraint but those would
                // just be trivial (but might cause useless cycles in fixpoint).
                // Nico: (This is probably ok because) We never do function
                // subtyping between `FnDef` *except* when (the def_id) is
                // passed as an argument to a function.
                for (arg_a, arg_b) in iter::zip(a_args, b_args) {
                    match (arg_a, arg_b) {
                        (GenericArg::Ty(ty_a), GenericArg::Ty(ty_b)) => {
                            let bty_a = ty_a.as_bty_skipping_existentials();
                            let bty_b = ty_b.as_bty_skipping_existentials();
                            tracked_span_dbg_assert_eq!(bty_a, bty_b);
                        }
                        (GenericArg::Base(ctor_a), GenericArg::Base(ctor_b)) => {
                            let bty_a = ctor_a.as_bty_skipping_binder();
                            let bty_b = ctor_b.as_bty_skipping_binder();
                            tracked_span_dbg_assert_eq!(bty_a, bty_b);
                        }
                        (_, _) => tracked_span_dbg_assert_eq!(arg_a, arg_b),
                    }
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
            (_, BaseTy::Alias(AliasKind::Opaque, alias_ty_b)) => {
                if let BaseTy::Alias(AliasKind::Opaque, alias_ty_a) = a {
                    debug_assert_eq!(alias_ty_a.refine_args.len(), alias_ty_b.refine_args.len());
                    iter::zip(alias_ty_a.refine_args.iter(), alias_ty_b.refine_args.iter())
                        .for_each(|(expr_a, expr_b)| infcx.unify_exprs(expr_a, expr_b));
                }
                self.handle_opaque_type(infcx, a, alias_ty_b)
            }
            (
                BaseTy::Alias(AliasKind::Projection, alias_ty_a),
                BaseTy::Alias(AliasKind::Projection, alias_ty_b),
            ) => {
                debug_assert_eq!(alias_ty_a, alias_ty_b);
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
                tracked_span_assert_eq!(preds_a.erase_regions(), preds_b.erase_regions());
                Ok(())
            }
            (BaseTy::Closure(did1, tys_a, _), BaseTy::Closure(did2, tys_b, _)) if did1 == did2 => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            (BaseTy::FnPtr(sig_a), BaseTy::FnPtr(sig_b)) => {
                tracked_span_assert_eq!(sig_a, sig_b);
                Ok(())
            }
            _ => Err(query_bug!("incompatible base types: `{a:?}` - `{b:?}`"))?,
        }
    }

    fn generic_args(
        &mut self,
        infcx: &mut InferCtxt,
        variance: Variance,
        a: &GenericArg,
        b: &GenericArg,
    ) -> InferResult {
        let (ty_a, ty_b) = match (a, b) {
            (GenericArg::Ty(ty_a), GenericArg::Ty(ty_b)) => (ty_a.clone(), ty_b.clone()),
            (GenericArg::Base(ctor_a), GenericArg::Base(ctor_b)) => {
                debug_assert_eq!(ctor_a.sort(), ctor_b.sort());
                (ctor_a.to_ty(), ctor_b.to_ty())
            }
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => return Ok(()),
            (GenericArg::Const(cst_a), GenericArg::Const(cst_b)) => {
                debug_assert_eq!(cst_a, cst_b);
                return Ok(());
            }
            _ => Err(query_bug!("incompatible generic args: `{a:?}` `{b:?}`"))?,
        };
        match variance {
            Variance::Covariant => self.tys(infcx, &ty_a, &ty_b),
            Variance::Invariant => {
                self.tys(infcx, &ty_a, &ty_b)?;
                self.tys(infcx, &ty_b, &ty_a)
            }
            Variance::Contravariant => self.tys(infcx, &ty_b, &ty_a),
            Variance::Bivariant => Ok(()),
        }
    }

    fn idxs_eq(&mut self, infcx: &mut InferCtxt, a: &Expr, b: &Expr) {
        if a == b {
            return;
        }

        match (a.kind(), b.kind()) {
            (ExprKind::Aggregate(kind_a, flds_a), ExprKind::Aggregate(kind_b, flds_b)) => {
                debug_assert_eq!(kind_a, kind_b);
                for (a, b) in iter::zip(flds_a, flds_b) {
                    self.idxs_eq(infcx, a, b);
                }
            }
            (_, ExprKind::Aggregate(kind_b, flds_b)) => {
                for (f, b) in flds_b.iter().enumerate() {
                    let a = a.proj_and_reduce(kind_b.to_proj(f as u32));
                    self.idxs_eq(infcx, &a, b);
                }
            }
            (ExprKind::Aggregate(kind_a, flds_a), _) => {
                infcx.unify_exprs(a, b);
                for (f, a) in flds_a.iter().enumerate() {
                    let b = b.proj_and_reduce(kind_a.to_proj(f as u32));
                    self.idxs_eq(infcx, a, &b);
                }
            }
            (ExprKind::Abs(lam_a), ExprKind::Abs(lam_b)) => {
                self.abs_eq(infcx, lam_a, lam_b);
            }
            (_, ExprKind::Abs(lam_b)) => {
                self.abs_eq(infcx, &a.eta_expand_abs(lam_b.vars(), lam_b.output()), lam_b);
            }
            (ExprKind::Abs(lam_a), _) => {
                infcx.unify_exprs(a, b);
                self.abs_eq(infcx, lam_a, &b.eta_expand_abs(lam_a.vars(), lam_a.output()));
            }
            (ExprKind::KVar(_), _) | (_, ExprKind::KVar(_)) => {
                infcx.check_impl(a, b, self.tag());
                infcx.check_impl(b, a, self.tag());
            }
            _ => {
                infcx.unify_exprs(a, b);
                let span = b.span();
                infcx.check_pred(Expr::binary_op(rty::BinOp::Eq, a, b).at_opt(span), self.tag());
            }
        }
    }

    fn abs_eq(&mut self, infcx: &mut InferCtxt, a: &Lambda, b: &Lambda) {
        debug_assert_eq!(a.vars().len(), b.vars().len());
        let vars = a
            .vars()
            .iter()
            .map(|kind| infcx.define_vars(kind.expect_sort()))
            .collect_vec();
        let body_a = a.apply(&vars);
        let body_b = b.apply(&vars);
        self.idxs_eq(infcx, &body_a, &body_b);
    }

    fn handle_opaque_type(
        &mut self,
        infcx: &mut InferCtxt,
        bty: &BaseTy,
        alias_ty: &AliasTy,
    ) -> InferResult {
        if let BaseTy::Coroutine(def_id, resume_ty, upvar_tys) = bty {
            let obligs = mk_coroutine_obligations(
                infcx.genv,
                def_id,
                resume_ty,
                upvar_tys,
                &alias_ty.def_id,
            )?;
            self.obligations.extend(obligs);
        } else {
            let bounds = infcx.genv.item_bounds(alias_ty.def_id)?.instantiate(
                infcx.tcx(),
                &alias_ty.args,
                &alias_ty.refine_args,
            );
            for clause in &bounds {
                if let rty::ClauseKind::Projection(pred) = clause.kind_skipping_binder() {
                    let ty1 = Self::project_ty(infcx, bty, pred.projection_ty.def_id)?;
                    let ty2 = pred.term.to_ty();
                    self.tys(infcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }

    fn project_ty(infcx: &InferCtxt, self_ty: &BaseTy, assoc_item_id: DefId) -> InferResult<Ty> {
        let args = List::singleton(GenericArg::Base(self_ty.to_subset_ty_ctor()));
        let alias_ty = rty::AliasTy::new(assoc_item_id, args, List::empty());
        Ok(BaseTy::Alias(AliasKind::Projection, alias_ty)
            .to_ty()
            .normalize_projections(infcx.genv, infcx.region_infcx, infcx.def_id)?)
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
                output: output.to_ty(),
            };
            let clause = rty::Clause::new(vec![], rty::ClauseKind::CoroutineOblig(pred));
            return Ok(vec![clause]);
        }
    }
    bug!("no projection predicate")
}

#[derive(Debug)]
pub enum InferErr {
    UnsolvedEvar(EVar),
    Query(QueryErr),
}

impl From<UnsolvedEvar> for InferErr {
    fn from(err: UnsolvedEvar) -> Self {
        InferErr::UnsolvedEvar(err.evar)
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
