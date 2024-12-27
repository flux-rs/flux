use std::{cell::RefCell, fmt, iter};

use flux_common::{bug, dbg, index::IndexVec, tracked_span_assert_eq, tracked_span_dbg_assert_eq};
use flux_config::{self as config, InferOpts};
use flux_middle::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self, canonicalize::Hoister, fold::TypeFoldable, AliasKind, AliasTy, BaseTy, Binder,
        BoundVariableKinds, CoroutineObligPredicate, ESpan, EVid, EarlyBinder, Expr, ExprKind,
        GenericArg, GenericArgs, HoleKind, InferMode, Lambda, List, Loc, Mutability, Name, Path,
        PolyVariant, PtrKind, RefineArgs, RefineArgsExt, Region, Sort, Ty, TyKind, Var,
    },
    MaybeExternId,
};
use itertools::{izip, Itertools};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::extension;
use rustc_middle::{
    mir::BasicBlock,
    ty::{TyCtxt, Variance},
};
use rustc_span::Span;

use crate::{
    fixpoint_encoding::{FixQueryCache, FixpointCtxt, KVarEncoding, KVarGen},
    refine_tree::{AssumeInvariants, RefineCtxt, RefineTree, Scope, Snapshot, Unpacker},
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
pub enum SubtypeReason {
    Input,
    Output,
    Requires,
    Ensures,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum ConstrReason {
    Call,
    Assign,
    Ret,
    Fold,
    FoldLocal,
    Assert(&'static str),
    Div,
    Rem,
    Goto(BasicBlock),
    Overflow,
    Subtype(SubtypeReason),
    Other,
}

pub struct InferCtxtRoot<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    inner: RefCell<InferCtxtInner>,
    refine_tree: RefineTree,
    opts: InferOpts,
}

pub struct InferCtxtRootBuilder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    opts: InferOpts,
    root_id: DefId,
    generic_args: Option<GenericArgs>,
    dummy_kvars: bool,
}

#[extension(pub trait GlobalEnvExt<'genv, 'tcx>)]
impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    fn infcx_root(self, root_id: DefId, opts: InferOpts) -> InferCtxtRootBuilder<'genv, 'tcx> {
        InferCtxtRootBuilder { genv: self, root_id, opts, generic_args: None, dummy_kvars: false }
    }
}

impl<'genv, 'tcx> InferCtxtRootBuilder<'genv, 'tcx> {
    pub fn with_dummy_kvars(mut self) -> Self {
        self.dummy_kvars = true;
        self
    }

    pub fn with_generic_args(mut self, generic_args: &GenericArgs) -> Self {
        self.generic_args = Some(generic_args.clone());
        self
    }

    pub fn build(self) -> QueryResult<InferCtxtRoot<'genv, 'tcx>> {
        let genv = self.genv;
        let mut params = genv
            .generics_of(self.root_id)?
            .const_params(genv)?
            .into_iter()
            .map(|(pcst, sort)| (Var::ConstGeneric(pcst), sort))
            .collect_vec();
        let offset = params.len();
        self.genv.refinement_generics_of(self.root_id)?.fill_item(
            self.genv,
            &mut params,
            &mut |param, index| {
                let index = (index - offset) as u32;
                let param = if let Some(args) = &self.generic_args {
                    param.instantiate(genv.tcx(), args, &[])
                } else {
                    param.instantiate_identity()
                };
                let var = Var::EarlyParam(rty::EarlyReftParam { index, name: param.name });
                (var, param.sort)
            },
        )?;

        Ok(InferCtxtRoot {
            genv: self.genv,
            inner: RefCell::new(InferCtxtInner::new(self.dummy_kvars)),
            refine_tree: RefineTree::new(params),
            opts: self.opts,
        })
    }
}

impl<'genv, 'tcx> InferCtxtRoot<'genv, 'tcx> {
    pub fn infcx<'a>(
        &'a mut self,
        def_id: DefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt {
            genv: self.genv,
            region_infcx,
            def_id,
            rcx: self.refine_tree.refine_ctxt_at_root(),
            inner: &self.inner,
            check_overflow: self.opts.check_overflow,
        }
    }

    pub fn fresh_kvar_in_scope(
        &self,
        binders: &[BoundVariableKinds],
        scope: &Scope,
        encoding: KVarEncoding,
    ) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner.kvars.fresh(binders, scope.iter(), encoding)
    }

    pub fn execute_fixpoint_query(
        self,
        cache: &mut FixQueryCache,
        def_id: MaybeExternId,
        ext: &'static str,
    ) -> QueryResult<Vec<Tag>> {
        let mut refine_tree = self.refine_tree;
        let kvars = self.inner.into_inner().kvars;
        if config::dump_constraint() {
            dbg::dump_item_info(self.genv.tcx(), def_id.resolved_id(), ext, &refine_tree).unwrap();
        }
        refine_tree.simplify(self.genv.spec_func_defns()?);
        if config::dump_constraint() {
            let simp_ext = format!("simp.{}", ext);
            dbg::dump_item_info(self.genv.tcx(), def_id.resolved_id(), simp_ext, &refine_tree)
                .unwrap();
        }

        let mut fcx = FixpointCtxt::new(self.genv, def_id, kvars);
        let cstr = refine_tree.into_fixpoint(&mut fcx)?;

        let backend = match self.opts.solver {
            flux_config::SmtSolver::Z3 => liquid_fixpoint::SmtSolver::Z3,
            flux_config::SmtSolver::CVC5 => liquid_fixpoint::SmtSolver::CVC5,
        };

        fcx.check(cache, cstr, self.opts.scrape_quals, backend)
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
    pub check_overflow: bool,
}

struct InferCtxtInner {
    kvars: KVarGen,
    evars: EVarStore,
}

impl InferCtxtInner {
    fn new(dummy_kvars: bool) -> Self {
        Self { kvars: KVarGen::new(dummy_kvars), evars: Default::default() }
    }
}

impl<'infcx, 'genv, 'tcx> InferCtxt<'infcx, 'genv, 'tcx> {
    pub fn at(&mut self, span: Span) -> InferCtxtAt<'_, 'infcx, 'genv, 'tcx> {
        InferCtxtAt { infcx: self, span }
    }

    pub fn instantiate_refine_args(
        &mut self,
        callee_def_id: DefId,
        args: &[rty::GenericArg],
    ) -> InferResult<List<Expr>> {
        Ok(RefineArgs::for_item(self.genv, callee_def_id, |param, _| {
            let param = param.instantiate(self.genv.tcx(), args, &[]);
            self.fresh_infer_var(&param.sort, param.mode)
        })?)
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
            InferMode::EVar => self.fresh_evar(),
        }
    }

    pub fn fresh_infer_var_for_hole(
        &mut self,
        binders: &[BoundVariableKinds],
        kind: HoleKind,
    ) -> Expr {
        match kind {
            HoleKind::Pred => self.fresh_kvar(binders, KVarEncoding::Conj),
            HoleKind::Expr(_) => {
                // We only use expression holes to infer early param arguments for opaque types
                // at function calls. These should be well-scoped in the current scope, so we ignore
                // the extra `binders` around the hole.
                self.fresh_evar()
            }
        }
    }

    /// Generate a fresh kvar in the current scope. See [`KVarGen::fresh`].
    pub fn fresh_kvar(&self, binders: &[BoundVariableKinds], encoding: KVarEncoding) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner.kvars.fresh(binders, self.rcx.vars(), encoding)
    }

    fn fresh_evar(&self) -> Expr {
        let evars = &mut self.inner.borrow_mut().evars;
        Expr::evar(evars.fresh(&self.rcx))
    }

    pub fn unify_exprs(&self, a: &Expr, b: &Expr) {
        if a.has_evars() {
            return;
        }

        let evars = &mut self.inner.borrow_mut().evars;
        if let ExprKind::Var(Var::EVar(evid)) = b.kind()
            && let EVarState::Unsolved(snapshot) = evars.get(*evid)
            && snapshot.has_free_vars(a)
        {
            evars.solve(*evid, a.clone());
        }
    }

    fn enter_exists<T, U>(&mut self, exists: &Binder<T>, f: impl FnOnce(&mut Self, T) -> U) -> U
    where
        T: TypeFoldable,
    {
        let a = 0;
        let t = exists.replace_bound_refts_with(|sort, mode, _| self.fresh_infer_var(sort, mode));
        let t = f(self, t);
        t
    }

    // The `InferCtxt` is a cursor into a tree. Some functions like `define_var`, `assume_pred` and
    // by extension `unpack` advance the cursor. For example, defining a variable pushes a node
    // as a child of the current node and then moves the cursor into that new node. Other functions,
    // like `subtyping` or `check_pred` (typically the ones defined in `InferCtxtAt`) do not advance
    // the cursor (from the caller's perspective). For example, if you call subtyping a subtree is
    // pushed under the current node, and the cursor is returned to where it was. That's the purpose
    // of infcx.branch: to "clone" the cursor such that the original one doesn't get modified.
    // `infcx.pop_scope()` and `infcx.replace_evars(...)` are supposed to be called when the `infcx`
    // is on the same node where the `push_scope` was called, because `replace_evars` only replaces
    // evars below that node. If `pop_scope` is called at a node further down (e.g. after calling
    // `unpack`), the evars above that cursor will not be replaced.
    // (see <https://github.com/flux-rs/flux/pull/900#discussion_r1853052650>)
    // pub fn push_scope(&mut self) {
    //     let scope = self.scope();
    //     self.inner.borrow_mut().evars.enter_context(scope);
    // }

    // pub fn pop_scope(&mut self) -> InferResult<EVarSol> {
    //     todo!()
    //     // let evars = &mut self.inner.borrow_mut().evars;
    //     // evars.exit_context();
    //     // Ok(evars.try_solve_pending()?)
    // }

    pub fn push_evar_scope(&mut self) {
        let a = 0;
    }

    pub fn pop_evar_scope(&mut self) -> InferResult {
        let a = 0;
        Ok(())
    }

    fn pop_evar_scope_without_solving_evars(&mut self) {
        let a = 0;
        todo!()
        // self.inner.borrow_mut().evars.exit_context();
    }

    pub fn fully_resolve_evars<T: TypeFoldable>(&self, t: &T) -> T {
        // document and finish implementing
        t.replace_evars(&mut |evid| None).unwrap()
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.genv.tcx()
    }

    pub fn rcx(&self) -> &RefineCtxt<'infcx> {
        &self.rcx
    }
}

/// Methods that modify or advance the [`RefineTree`] cursor
impl<'infcx, 'genv, 'tcx> InferCtxt<'infcx, 'genv, 'tcx> {
    pub fn change_item<'a>(
        &'a mut self,
        def_id: LocalDefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt { def_id: def_id.to_def_id(), rcx: self.rcx.branch(), region_infcx, ..*self }
    }

    pub fn change_root(
        &mut self,
        snapshot: &Snapshot,
        clear_children: bool,
    ) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt { rcx: self.rcx.change_root(snapshot, clear_children).unwrap(), ..*self }
    }

    pub fn branch(&mut self) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt { rcx: self.rcx.branch(), ..*self }
    }

    pub fn define_vars(&mut self, sort: &Sort) -> Expr {
        self.rcx.define_vars(sort)
    }

    pub fn define_var(&mut self, sort: &Sort) -> Name {
        self.rcx.define_var(sort)
    }

    pub fn check_pred(&mut self, pred: impl Into<Expr>, tag: Tag) {
        self.rcx.check_pred(pred, tag);
    }

    // pub fn replace_evars(&mut self, evars: &EVarSol) {
    //     self.rcx.replace_evars(evars);
    // }

    pub fn assume_pred(&mut self, pred: impl Into<Expr>) {
        self.rcx.assume_pred(pred);
    }

    pub fn unpack(&mut self, ty: &Ty) -> Ty {
        self.hoister(false).hoist(ty)
    }

    pub fn snapshot(&self) -> Snapshot {
        self.rcx.snapshot()
    }

    pub fn hoister(&mut self, assume_invariants: bool) -> Hoister<Unpacker<'_, 'infcx>> {
        self.rcx.hoister(if assume_invariants {
            AssumeInvariants::yes(self.check_overflow)
        } else {
            AssumeInvariants::No
        })
    }

    pub fn assume_invariants(&mut self, ty: &Ty) {
        self.rcx.assume_invariants(ty, self.check_overflow);
    }

    fn check_impl(&mut self, pred1: impl Into<Expr>, pred2: impl Into<Expr>, tag: Tag) {
        self.rcx.check_impl(pred1, pred2, tag);
    }
}

#[derive(Default)]
struct EVarStore {
    evars: IndexVec<EVid, EVarState>,
}

enum EVarState {
    Solved(Expr),
    Unsolved(Snapshot),
}

impl EVarStore {
    fn fresh(&mut self, rcx: &RefineCtxt) -> EVid {
        self.evars.push(EVarState::Unsolved(rcx.snapshot()))
    }

    fn solve(&mut self, evid: EVid, expr: Expr) {
        debug_assert!(matches!(self.evars[evid], EVarState::Unsolved(_)));
        self.evars[evid] = EVarState::Solved(expr);
    }

    fn get(&self, evid: EVid) -> &EVarState {
        &self.evars[evid]
    }
}

impl std::fmt::Debug for InferCtxt<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.rcx, f)
    }
}

#[derive(Debug)]
pub struct InferCtxtAt<'a, 'infcx, 'genv, 'tcx> {
    pub infcx: &'a mut InferCtxt<'infcx, 'genv, 'tcx>,
    pub span: Span,
}

impl InferCtxtAt<'_, '_, '_, '_> {
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

    /// Relate types via subtyping. This is the same as [`InferCtxtAt::subtyping`] except that we
    /// also require a [`LocEnv`] to handle pointers and strong references
    pub fn subtyping_with_env(
        &mut self,
        env: &mut impl LocEnv,
        a: &Ty,
        b: &Ty,
        reason: ConstrReason,
    ) -> InferResult {
        let mut sub = Sub::new(env, reason, self.span);
        sub.tys(self.infcx, a, b)
    }

    /// Relate types via subtyping and returns coroutine obligations. This doesn't handle subtyping
    /// when strong references are involved.
    ///
    /// See comment for [`Sub::obligations`].
    pub fn subtyping(
        &mut self,
        a: &Ty,
        b: &Ty,
        reason: ConstrReason,
    ) -> InferResult<Vec<Binder<rty::CoroutineObligPredicate>>> {
        let mut env = DummyEnv;
        let mut sub = Sub::new(&mut env, reason, self.span);
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
        self.infcx.push_evar_scope();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = self.infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(self.infcx.tcx(), &generic_args, &[])
            .replace_bound_refts_with(|sort, mode, _| self.infcx.fresh_infer_var(sort, mode));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            self.subtyping(actual, formal, reason)?;
        }

        // Ensure all evars all solved
        self.infcx.pop_evar_scope()?;

        Ok(self.infcx.fully_resolve_evars(&variant.ret()))
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

    pub(crate) fn replace_evars(
        &mut self,
        f: &mut impl FnMut(EVid) -> Option<Expr>,
    ) -> Result<(), EVid> {
        match self {
            TypeTrace::Types(a, b) => {
                *self = TypeTrace::Types(a.replace_evars(f)?, b.replace_evars(f)?);
            }
            TypeTrace::BaseTys(a, b) => {
                *self = TypeTrace::BaseTys(a.replace_evars(f)?, b.replace_evars(f)?);
            }
        }
        Ok(())
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

struct DummyEnv;

impl LocEnv for DummyEnv {
    fn ptr_to_ref(
        &mut self,
        _: &mut InferCtxtAt,
        _: ConstrReason,
        _: Region,
        _: &Path,
        _: Ty,
    ) -> InferResult<Ty> {
        bug!("call to `ptr_to_ref` on `DummyEnv`")
    }

    fn unfold_strg_ref(&mut self, _: &mut InferCtxt, _: &Path, _: &Ty) -> InferResult<Loc> {
        bug!("call to `unfold_str_ref` on `DummyEnv`")
    }

    fn get(&self, _: &Path) -> Ty {
        bug!("call to `get` on `DummyEnv`")
    }
}

/// Context used to relate two types `a` and `b` via subtyping
struct Sub<'a, E> {
    /// The environment to lookup locations pointed to by [`TyKind::Ptr`].
    env: &'a mut E,
    reason: ConstrReason,
    span: Span,
    /// FIXME(nilehmann) This is used to store coroutine obligations generated during subtyping when
    /// relating an opaque type. Other obligations related to relating opaque types are resolved
    /// directly here. The implementation is really messy and we may be missing some obligations.
    obligations: Vec<Binder<rty::CoroutineObligPredicate>>,
}

impl<'a, E: LocEnv> Sub<'a, E> {
    fn new(env: &'a mut E, reason: ConstrReason, span: Span) -> Self {
        Self { env, reason, span, obligations: vec![] }
    }

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

            (TyKind::Ptr(PtrKind::Mut(_), path_a), TyKind::StrgRef(_, path_b, ty_b)) => {
                // We should technically remove `path1` from `env`, but we are assuming that functions
                // always give back ownership of the location so `path1` is going to be overwritten
                // after the call anyways.
                let ty_a = self.env.get(path_a);
                infcx.unify_exprs(&path_a.to_expr(), &path_b.to_expr());
                self.tys(infcx, &ty_a, ty_b)
            }
            (TyKind::StrgRef(_, path_a, ty_a), TyKind::StrgRef(_, path_b, ty_b)) => {
                // We have to unfold strong references prior to a subtyping check. Normally, when
                // checking a function body, a `StrgRef` is automatically unfolded i.e. `x:&strg T`
                // is turned into a `x:ptr(l); l: T` where `l` is some fresh location. However, we
                // need the below to do a similar unfolding during function subtyping where we just
                // have the super-type signature that needs to be unfolded. We also add the binding
                // to the environment so that we can:
                // (1) UPDATE the location after the call, and
                // (2) CHECK the relevant `ensures` clauses of the super-sig.
                // Same as the `Ptr` case above we should remove the location from the environment
                // after unfolding to consume it, but we are assuming functions always give back
                // ownership.
                self.env.unfold_strg_ref(infcx, path_a, ty_a)?;
                let ty_a = self.env.get(path_a);
                infcx.unify_exprs(&path_a.to_expr(), &path_b.to_expr());
                self.tys(infcx, &ty_a, ty_b)
            }
            (
                TyKind::Ptr(PtrKind::Mut(re), path),
                TyKind::Indexed(BaseTy::Ref(_, bound, Mutability::Mut), idx),
            ) => {
                // We sometimes generate evars for the index of references so we need to make sure
                // we solve them.
                self.idxs_eq(infcx, &Expr::unit(), idx);

                self.env.ptr_to_ref(
                    &mut infcx.at(self.span),
                    self.reason,
                    *re,
                    path,
                    bound.clone(),
                )?;
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
            (TyKind::Param(param_ty_a), TyKind::Param(param_ty_b)) => {
                debug_assert_eq!(param_ty_a, param_ty_b);
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
            (BaseTy::Float(float_ty_a), BaseTy::Float(float_ty_b)) => {
                debug_assert_eq!(float_ty_a, float_ty_b);
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
                    let alias_ty = pred.projection_ty.with_self_ty(bty.to_subset_ty_ctor());
                    let ty1 = BaseTy::Alias(AliasKind::Projection, alias_ty)
                        .to_ty()
                        .normalize_projections(infcx.genv, infcx.region_infcx, infcx.def_id)?;
                    let ty2 = pred.term.to_ty();
                    self.tys(infcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }
}

fn mk_coroutine_obligations(
    genv: GlobalEnv,
    generator_did: &DefId,
    resume_ty: &Ty,
    upvar_tys: &List<Ty>,
    opaque_def_id: &DefId,
) -> InferResult<Vec<Binder<rty::CoroutineObligPredicate>>> {
    let bounds = genv.item_bounds(*opaque_def_id)?.skip_binder();
    for bound in &bounds {
        if let Some(proj_clause) = bound.as_projection_clause() {
            return Ok(vec![proj_clause.map(|proj_clause| {
                let output = proj_clause.term;
                CoroutineObligPredicate {
                    def_id: *generator_did,
                    resume_ty: resume_ty.clone(),
                    upvar_tys: upvar_tys.clone(),
                    output: output.to_ty(),
                }
            })]);
        }
    }
    bug!("no projection predicate")
}

#[derive(Debug)]
pub enum InferErr {
    UnsolvedEvar(EVid),
    OpaqueStruct(DefId),
    Query(QueryErr),
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
            w!(cx, f, "{:?} at {:?}", ^self.reason, self.src_span)
        }
    }

    impl_debug_with_default_cx!(Tag);
}
