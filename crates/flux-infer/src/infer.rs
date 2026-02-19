use std::{cell::RefCell, fmt, iter};

use flux_common::{bug, dbg, tracked_span_assert_eq, tracked_span_bug, tracked_span_dbg_assert_eq};
use flux_config::{self as config, InferOpts, OverflowMode, RawDerefMode};
use flux_macros::{TypeFoldable, TypeVisitable};
use flux_middle::{
    FixpointQueryKind,
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    metrics::{self, Metric},
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self, AliasKind, AliasTy, BaseTy, Binder, BoundReftKind, BoundVariableKinds,
        CoroutineObligPredicate, Ctor, ESpan, EVid, EarlyBinder, Expr, ExprKind, FieldProj,
        GenericArg, HoleKind, InferMode, Lambda, List, Loc, Mutability, Name, NameProvenance, Path,
        PolyVariant, PtrKind, RefineArgs, RefineArgsExt, Region, Sort, Ty, TyCtor, TyKind, Var,
        canonicalize::{Hoister, HoisterDelegate},
        fold::TypeFoldable,
    },
};
use itertools::{Itertools, izip};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::extension;
use rustc_middle::{
    mir::BasicBlock,
    ty::{TyCtxt, Variance},
};
use rustc_span::{Span, Symbol};
use rustc_type_ir::Variance::Invariant;

use crate::{
    evars::{EVarState, EVarStore},
    fixpoint_encoding::{
        Answer, Backend, FixQueryCache, FixpointCtxt, KVarEncoding, KVarGen, KVarSolutions,
    },
    projections::NormalizeExt as _,
    refine_tree::{Cursor, Marker, RefineTree, Scope},
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
    Predicate,
    Assert(&'static str),
    Div,
    Rem,
    Goto(BasicBlock),
    Overflow,
    Underflow,
    Subtype(SubtypeReason),
    NoPanic(DefId),
    Other,
}

pub struct InferCtxtRoot<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    inner: RefCell<InferCtxtInner>,
    refine_tree: RefineTree,
    opts: InferOpts,
}

pub struct InferCtxtRootBuilder<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    opts: InferOpts,
    params: Vec<(Var, Sort)>,
    infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    dummy_kvars: bool,
}

#[extension(pub trait GlobalEnvExt<'genv, 'tcx>)]
impl<'genv, 'tcx> GlobalEnv<'genv, 'tcx> {
    fn infcx_root<'a>(
        self,
        infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        opts: InferOpts,
    ) -> InferCtxtRootBuilder<'a, 'genv, 'tcx> {
        InferCtxtRootBuilder { genv: self, infcx, params: vec![], opts, dummy_kvars: false }
    }
}

impl<'genv, 'tcx> InferCtxtRootBuilder<'_, 'genv, 'tcx> {
    pub fn with_dummy_kvars(mut self) -> Self {
        self.dummy_kvars = true;
        self
    }

    pub fn with_const_generics(mut self, def_id: DefId) -> QueryResult<Self> {
        self.params.extend(
            self.genv
                .generics_of(def_id)?
                .const_params(self.genv)?
                .into_iter()
                .map(|(pcst, sort)| (Var::ConstGeneric(pcst), sort)),
        );
        Ok(self)
    }

    pub fn with_refinement_generics(
        mut self,
        def_id: DefId,
        args: &[GenericArg],
    ) -> QueryResult<Self> {
        for (index, param) in self
            .genv
            .refinement_generics_of(def_id)?
            .iter_own_params()
            .enumerate()
        {
            let param = param.instantiate(self.genv.tcx(), args, &[]);
            let sort = param
                .sort
                .deeply_normalize_sorts(def_id, self.genv, self.infcx)?;

            let var =
                Var::EarlyParam(rty::EarlyReftParam { index: index as u32, name: param.name });
            self.params.push((var, sort));
        }
        Ok(self)
    }

    pub fn identity_for_item(mut self, def_id: DefId) -> QueryResult<Self> {
        self = self.with_const_generics(def_id)?;
        let offset = self.params.len();
        self.genv.refinement_generics_of(def_id)?.fill_item(
            self.genv,
            &mut self.params,
            &mut |param, index| {
                let index = (index - offset) as u32;
                let param = param.instantiate_identity();
                let sort = param
                    .sort
                    .deeply_normalize_sorts(def_id, self.genv, self.infcx)?;

                let var = Var::EarlyParam(rty::EarlyReftParam { index, name: param.name });
                Ok((var, sort))
            },
        )?;
        Ok(self)
    }

    pub fn build(self) -> QueryResult<InferCtxtRoot<'genv, 'tcx>> {
        Ok(InferCtxtRoot {
            genv: self.genv,
            inner: RefCell::new(InferCtxtInner::new(self.dummy_kvars)),
            refine_tree: RefineTree::new(self.params),
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
            cursor: self.refine_tree.cursor_at_root(),
            inner: &self.inner,
            check_overflow: self.opts.check_overflow,
            allow_raw_deref: self.opts.allow_raw_deref,
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

    pub fn execute_lean_query(
        self,
        cache: &mut FixQueryCache,
        def_id: MaybeExternId,
    ) -> QueryResult {
        let inner = self.inner.into_inner();
        let kvars = inner.kvars;
        let evars = inner.evars;
        let mut refine_tree = self.refine_tree;
        refine_tree.replace_evars(&evars).unwrap();
        refine_tree.simplify(self.genv);

        let solver = match self.opts.solver {
            flux_config::SmtSolver::Z3 => liquid_fixpoint::SmtSolver::Z3,
            flux_config::SmtSolver::CVC5 => liquid_fixpoint::SmtSolver::CVC5,
        };
        let mut fcx = FixpointCtxt::new(self.genv, def_id, kvars, Backend::Lean);
        let cstr = refine_tree.to_fixpoint(&mut fcx)?;
        let cstr_variable_sorts = cstr.variable_sorts();
        let task = fcx.create_task(def_id, cstr, self.opts.scrape_quals, solver)?;
        let result = fcx.run_task(cache, def_id, FixpointQueryKind::Body, &task)?;

        fcx.generate_lean_files(
            def_id,
            task,
            KVarSolutions::closed_solutions(
                cstr_variable_sorts,
                result.solution,
                result.non_cut_solution,
            ),
        )
    }

    pub fn execute_fixpoint_query(
        self,
        cache: &mut FixQueryCache,
        def_id: MaybeExternId,
        kind: FixpointQueryKind,
    ) -> QueryResult<Answer<Tag>> {
        let inner = self.inner.into_inner();
        let kvars = inner.kvars;
        let evars = inner.evars;

        let ext = kind.ext();

        let mut refine_tree = self.refine_tree;

        refine_tree.replace_evars(&evars).unwrap();

        if config::dump_constraint() {
            dbg::dump_item_info(self.genv.tcx(), def_id.resolved_id(), ext, &refine_tree).unwrap();
        }
        refine_tree.simplify(self.genv);
        if config::dump_constraint() {
            let simp_ext = format!("simp.{ext}");
            dbg::dump_item_info(self.genv.tcx(), def_id.resolved_id(), simp_ext, &refine_tree)
                .unwrap();
        }

        let backend = match self.opts.solver {
            flux_config::SmtSolver::Z3 => liquid_fixpoint::SmtSolver::Z3,
            flux_config::SmtSolver::CVC5 => liquid_fixpoint::SmtSolver::CVC5,
        };

        let mut fcx = FixpointCtxt::new(self.genv, def_id, kvars, Backend::Fixpoint);
        let cstr = refine_tree.to_fixpoint(&mut fcx)?;

        // skip checking trivial constraints
        let count = cstr.concrete_head_count();
        metrics::incr_metric(Metric::CsTotal, count as u32);
        if count == 0 {
            metrics::incr_metric_if(kind.is_body(), Metric::FnTrivial);
            return Ok(Answer::trivial());
        }

        let task = fcx.create_task(def_id, cstr, self.opts.scrape_quals, backend)?;
        let result = fcx.run_task(cache, def_id, kind, &task)?;
        Ok(fcx.result_to_answer(result))
    }

    pub fn split(self) -> (RefineTree, KVarGen) {
        (self.refine_tree, self.inner.into_inner().kvars)
    }
}

pub struct InferCtxt<'infcx, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub region_infcx: &'infcx rustc_infer::infer::InferCtxt<'tcx>,
    pub def_id: DefId,
    pub check_overflow: OverflowMode,
    pub allow_raw_deref: flux_config::RawDerefMode,
    cursor: Cursor<'infcx>,
    inner: &'infcx RefCell<InferCtxtInner>,
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
            Ok(self.fresh_infer_var(&param.sort, param.mode))
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

    /// Generate a fresh kvar in the _given_ [`Scope`] (similar method in [`InferCtxtRoot`]).
    pub fn fresh_kvar_in_scope(
        &self,
        binders: &[BoundVariableKinds],
        scope: &Scope,
        encoding: KVarEncoding,
    ) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner.kvars.fresh(binders, scope.iter(), encoding)
    }

    /// Generate a fresh kvar in the current scope. See [`KVarGen::fresh`].
    pub fn fresh_kvar(&self, binders: &[BoundVariableKinds], encoding: KVarEncoding) -> Expr {
        let inner = &mut *self.inner.borrow_mut();
        inner.kvars.fresh(binders, self.cursor.vars(), encoding)
    }

    fn fresh_evar(&self) -> Expr {
        let evars = &mut self.inner.borrow_mut().evars;
        Expr::evar(evars.fresh(self.cursor.marker()))
    }

    pub fn unify_exprs(&self, a: &Expr, b: &Expr) {
        if a.has_evars() {
            return;
        }
        let evars = &mut self.inner.borrow_mut().evars;
        if let ExprKind::Var(Var::EVar(evid)) = b.kind()
            && let EVarState::Unsolved(marker) = evars.get(*evid)
            && !marker.has_free_vars(a)
        {
            evars.solve(*evid, a.clone());
        }
    }

    fn enter_exists<T, U>(
        &mut self,
        t: &Binder<T>,
        f: impl FnOnce(&mut InferCtxt<'_, 'genv, 'tcx>, T) -> U,
    ) -> U
    where
        T: TypeFoldable,
    {
        self.ensure_resolved_evars(|infcx| {
            let t = t.replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));
            Ok(f(infcx, t))
        })
        .unwrap()
    }

    /// Used in conjunction with [`InferCtxt::pop_evar_scope`] to ensure evars are solved at the end
    /// of some scope, for example, to ensure all evars generated during a function call are solved
    /// after checking argument subtyping. These functions can be used in a stack-like fashion to
    /// create nested scopes.
    pub fn push_evar_scope(&mut self) {
        self.inner.borrow_mut().evars.push_scope();
    }

    /// Pop a scope and check all evars have been solved. This only check evars generated from the
    /// last call to [`InferCtxt::push_evar_scope`].
    pub fn pop_evar_scope(&mut self) -> InferResult {
        self.inner
            .borrow_mut()
            .evars
            .pop_scope()
            .map_err(InferErr::UnsolvedEvar)
    }

    /// Convenience method pairing [`InferCtxt::push_evar_scope`] and [`InferCtxt::pop_evar_scope`].
    pub fn ensure_resolved_evars<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> InferResult<R>,
    ) -> InferResult<R> {
        self.push_evar_scope();
        let r = f(self)?;
        self.pop_evar_scope()?;
        Ok(r)
    }

    pub fn fully_resolve_evars<T: TypeFoldable>(&self, t: &T) -> T {
        self.inner.borrow().evars.replace_evars(t).unwrap()
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.genv.tcx()
    }

    pub fn cursor(&self) -> &Cursor<'infcx> {
        &self.cursor
    }

    pub fn allow_raw_deref(&self) -> bool {
        matches!(self.allow_raw_deref, RawDerefMode::Ok)
    }
}

/// Methods that interact with the underlying [`Cursor`]
impl<'infcx, 'genv, 'tcx> InferCtxt<'infcx, 'genv, 'tcx> {
    pub fn change_item<'a>(
        &'a mut self,
        def_id: LocalDefId,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt {
            def_id: def_id.to_def_id(),
            cursor: self.cursor.branch(),
            region_infcx,
            ..*self
        }
    }

    pub fn move_to(&mut self, marker: &Marker, clear_children: bool) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt {
            cursor: self
                .cursor
                .move_to(marker, clear_children)
                .unwrap_or_else(|| tracked_span_bug!()),
            ..*self
        }
    }

    pub fn branch(&mut self) -> InferCtxt<'_, 'genv, 'tcx> {
        InferCtxt { cursor: self.cursor.branch(), ..*self }
    }

    fn define_var(&mut self, sort: &Sort, provenance: NameProvenance) -> Name {
        self.cursor.define_var(sort, provenance)
    }

    pub fn define_bound_reft_var(&mut self, sort: &Sort, kind: BoundReftKind) -> Name {
        self.define_var(sort, NameProvenance::UnfoldBoundReft(kind))
    }

    pub fn define_unknown_var(&mut self, sort: &Sort) -> Name {
        self.cursor.define_var(sort, NameProvenance::Unknown)
    }

    pub fn check_pred(&mut self, pred: impl Into<Expr>, tag: Tag) {
        self.cursor.check_pred(pred, tag);
    }

    pub fn assume_pred(&mut self, pred: impl Into<Expr>) {
        self.cursor.assume_pred(pred);
    }

    pub fn unpack(&mut self, ty: &Ty) -> Ty {
        self.hoister(false).hoist(ty)
    }

    pub fn unpack_at_name(&mut self, name: Option<Symbol>, ty: &Ty) -> Ty {
        let mut hoister = self.hoister(false);
        hoister.delegate.name = name;
        hoister.hoist(ty)
    }

    pub fn marker(&self) -> Marker {
        self.cursor.marker()
    }

    pub fn hoister(
        &mut self,
        assume_invariants: bool,
    ) -> Hoister<Unpacker<'_, 'infcx, 'genv, 'tcx>> {
        Hoister::with_delegate(Unpacker { infcx: self, assume_invariants, name: None })
            .transparent()
    }

    pub fn assume_invariants(&mut self, ty: &Ty) {
        self.cursor
            .assume_invariants(self.genv.tcx(), ty, self.check_overflow);
    }

    fn check_impl(&mut self, pred1: impl Into<Expr>, pred2: impl Into<Expr>, tag: Tag) {
        self.cursor.check_impl(pred1, pred2, tag);
    }
}

pub struct Unpacker<'a, 'infcx, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'infcx, 'genv, 'tcx>,
    assume_invariants: bool,
    name: Option<Symbol>,
}

impl HoisterDelegate for Unpacker<'_, '_, '_, '_> {
    fn hoist_exists(&mut self, ty_ctor: &TyCtor) -> Ty {
        let ty = ty_ctor.replace_bound_refts_with(|sort, _, kind| {
            let kind = if let Some(name) = self.name { BoundReftKind::Named(name) } else { kind };
            Expr::fvar(self.infcx.define_bound_reft_var(sort, kind))
        });
        if self.assume_invariants {
            self.infcx.assume_invariants(&ty);
        }
        ty
    }

    fn hoist_constr(&mut self, pred: Expr) {
        self.infcx.assume_pred(pred);
    }
}

impl std::fmt::Debug for InferCtxt<'_, '_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.cursor, f)
    }
}

#[derive(Debug)]
pub struct InferCtxtAt<'a, 'infcx, 'genv, 'tcx> {
    pub infcx: &'a mut InferCtxt<'infcx, 'genv, 'tcx>,
    pub span: Span,
}

impl<'genv, 'tcx> InferCtxtAt<'_, '_, 'genv, 'tcx> {
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
                    .deeply_normalize(self)?;
                let term = projection_pred.term.to_ty().deeply_normalize(self)?;

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
    ) -> InferResult<Vec<Binder<rty::CoroutineObligPredicate>>> {
        let mut sub = Sub::new(env, reason, self.span);
        sub.tys(self.infcx, a, b)?;
        Ok(sub.obligations)
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

    pub fn subtyping_generic_args(
        &mut self,
        variance: Variance,
        a: &GenericArg,
        b: &GenericArg,
        reason: ConstrReason,
    ) -> InferResult<Vec<Binder<rty::CoroutineObligPredicate>>> {
        let mut env = DummyEnv;
        let mut sub = Sub::new(&mut env, reason, self.span);
        sub.generic_args(self.infcx, variance, a, b)?;
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
        let ret = self.ensure_resolved_evars(|this| {
            // Replace holes in generic arguments with fresh inference variables
            let generic_args = this.instantiate_generic_args(generic_args);

            let variant = variant
                .instantiate(this.tcx(), &generic_args, &[])
                .replace_bound_refts_with(|sort, mode, _| this.fresh_infer_var(sort, mode));

            // Check arguments
            for (actual, formal) in iter::zip(fields, variant.fields()) {
                this.subtyping(actual, formal, reason)?;
            }

            // Check requires predicates
            for require in &variant.requires {
                this.check_pred(require, ConstrReason::Fold);
            }

            Ok(variant.ret())
        })?;
        Ok(self.fully_resolve_evars(&ret))
    }

    pub fn ensure_resolved_evars<R>(
        &mut self,
        f: impl FnOnce(&mut InferCtxtAt<'_, '_, 'genv, 'tcx>) -> InferResult<R>,
    ) -> InferResult<R> {
        self.infcx
            .ensure_resolved_evars(|infcx| f(&mut infcx.at(self.span)))
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
#[derive(TypeVisitable, TypeFoldable)]
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
        tracked_span_bug!("call to `ptr_to_ref` on `DummyEnv`")
    }

    fn unfold_strg_ref(&mut self, _: &mut InferCtxt, _: &Path, _: &Ty) -> InferResult<Loc> {
        tracked_span_bug!("call to `unfold_str_ref` on `DummyEnv`")
    }

    fn get(&self, _: &Path) -> Ty {
        tracked_span_bug!("call to `get` on `DummyEnv`")
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
        // infcx.cursor.push_trace(TypeTrace::tys(a, b));

        // We *fully* unpack the lhs before continuing to be able to prove goals like this
        // ∃a. (i32[a], ∃b. {i32[b] | a > b})} <: ∃a,b. ({i32[a] | b < a}, i32[b])
        // See S4.5 in https://arxiv.org/pdf/2209.13000v1.pdf
        let a = infcx.unpack(a);

        match (a.kind(), b.kind()) {
            (TyKind::Exists(..), _) => {
                bug!("existentials should have been removed by the unpacking above");
            }
            (TyKind::Constr(..), _) => {
                bug!("constraint types should have been removed by the unpacking above");
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

            (BaseTy::RawPtr(ty_a, mut_a), BaseTy::RawPtr(ty_b, mut_b)) => {
                debug_assert_eq!(mut_a, mut_b);
                self.tys(infcx, ty_a, ty_b)?;
                if matches!(mut_a, Mutability::Mut) {
                    self.tys(infcx, ty_b, ty_a)?;
                }
                Ok(())
            }

            (BaseTy::Ref(_, ty_a, Mutability::Mut), BaseTy::Ref(_, ty_b, Mutability::Mut)) => {
                if ty_a.is_slice()
                    && let TyKind::Indexed(_, idx_a) = ty_a.kind()
                    && let TyKind::Exists(bty_b) = ty_b.kind()
                {
                    // For `&mut [T1][e] <: &mut ∃v[T2][v]`, we can hoist out the existential on the right because we know
                    // the index is immutable. This means we have to prove `&mut [T1][e] <: ∃v. &mut [T2][v]`
                    // This will in turn require proving `&mut [T1][e1] <: &mut [T2][?v]` for a fresh evar `?v`.
                    // We know the evar will solve to `e`, so subtyping simplifies to the bellow.
                    self.tys(infcx, ty_a, ty_b)?;
                    self.tys(infcx, &bty_b.replace_bound_reft(idx_a), ty_a)
                } else {
                    self.tys(infcx, ty_a, ty_b)?;
                    self.tys(infcx, ty_b, ty_a)
                }
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
            (
                BaseTy::Alias(AliasKind::Opaque, alias_ty_a),
                BaseTy::Alias(AliasKind::Opaque, alias_ty_b),
            ) => {
                debug_assert_eq!(alias_ty_a.def_id, alias_ty_b.def_id);

                // handle type-args
                for (ty_a, ty_b) in izip!(alias_ty_a.args.iter(), alias_ty_b.args.iter()) {
                    self.generic_args(infcx, Invariant, ty_a, ty_b)?;
                }

                // handle refine-args
                debug_assert_eq!(alias_ty_a.refine_args.len(), alias_ty_b.refine_args.len());
                iter::zip(alias_ty_a.refine_args.iter(), alias_ty_b.refine_args.iter())
                    .for_each(|(expr_a, expr_b)| infcx.unify_exprs(expr_a, expr_b));

                Ok(())
            }
            (_, BaseTy::Alias(AliasKind::Opaque, alias_ty_b)) => {
                // only for when concrete type on LHS and impl-with-bounds on RHS
                self.handle_opaque_type(infcx, a, alias_ty_b)
            }
            (
                BaseTy::Alias(AliasKind::Projection, alias_ty_a),
                BaseTy::Alias(AliasKind::Projection, alias_ty_b),
            ) => {
                tracked_span_dbg_assert_eq!(alias_ty_a.erase_regions(), alias_ty_b.erase_regions());
                Ok(())
            }
            (BaseTy::Array(ty_a, len_a), BaseTy::Array(ty_b, len_b)) => {
                tracked_span_dbg_assert_eq!(len_a, len_b);
                self.tys(infcx, ty_a, ty_b)
            }
            (BaseTy::Param(param_a), BaseTy::Param(param_b)) => {
                debug_assert_eq!(param_a, param_b);
                Ok(())
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtrMetadata(_), BaseTy::RawPtrMetadata(_)) => Ok(()),
            (BaseTy::Dynamic(preds_a, _), BaseTy::Dynamic(preds_b, _)) => {
                tracked_span_assert_eq!(preds_a.erase_regions(), preds_b.erase_regions());
                Ok(())
            }
            (BaseTy::Closure(did1, tys_a, _, _), BaseTy::Closure(did2, tys_b, _, _))
                if did1 == did2 =>
            {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                Ok(())
            }
            (BaseTy::FnPtr(sig_a), BaseTy::FnPtr(sig_b)) => {
                tracked_span_assert_eq!(sig_a.erase_regions(), sig_b.erase_regions());
                Ok(())
            }
            (BaseTy::Never, BaseTy::Never) => Ok(()),
            (
                BaseTy::Coroutine(did1, resume_ty_a, tys_a, _),
                BaseTy::Coroutine(did2, resume_ty_b, tys_b, _),
            ) if did1 == did2 => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.tys(infcx, ty_a, ty_b)?;
                }
                // TODO(RJ): Treating resume type as invariant...but I think they should be contravariant(?)
                self.tys(infcx, resume_ty_b, resume_ty_a)?;
                self.tys(infcx, resume_ty_a, resume_ty_b)?;

                Ok(())
            }
            (BaseTy::Foreign(did_a), BaseTy::Foreign(did_b)) if did_a == did_b => Ok(()),
            _ => Err(query_bug!("incompatible base types: `{a:#?}` - `{b:#?}`"))?,
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
                tracked_span_dbg_assert_eq!(
                    ctor_a.sort().erase_regions(),
                    ctor_b.sort().erase_regions()
                );
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
            (
                ExprKind::Ctor(Ctor::Struct(did_a), flds_a),
                ExprKind::Ctor(Ctor::Struct(did_b), flds_b),
            ) => {
                debug_assert_eq!(did_a, did_b);
                for (a, b) in iter::zip(flds_a, flds_b) {
                    self.idxs_eq(infcx, a, b);
                }
            }
            (ExprKind::Tuple(flds_a), ExprKind::Tuple(flds_b)) => {
                for (a, b) in iter::zip(flds_a, flds_b) {
                    self.idxs_eq(infcx, a, b);
                }
            }
            (_, ExprKind::Tuple(flds_b)) => {
                for (f, b) in flds_b.iter().enumerate() {
                    let proj = FieldProj::Tuple { arity: flds_b.len(), field: f as u32 };
                    let a = a.proj_and_reduce(proj);
                    self.idxs_eq(infcx, &a, b);
                }
            }

            (_, ExprKind::Ctor(Ctor::Struct(def_id), flds_b)) => {
                for (f, b) in flds_b.iter().enumerate() {
                    let proj = FieldProj::Adt { def_id: *def_id, field: f as u32 };
                    let a = a.proj_and_reduce(proj);
                    self.idxs_eq(infcx, &a, b);
                }
            }

            (ExprKind::Tuple(flds_a), _) => {
                infcx.unify_exprs(a, b);
                for (f, a) in flds_a.iter().enumerate() {
                    let proj = FieldProj::Tuple { arity: flds_a.len(), field: f as u32 };
                    let b = b.proj_and_reduce(proj);
                    self.idxs_eq(infcx, a, &b);
                }
            }
            (ExprKind::Ctor(Ctor::Struct(def_id), flds_a), _) => {
                infcx.unify_exprs(a, b);
                for (f, a) in flds_a.iter().enumerate() {
                    let proj = FieldProj::Adt { def_id: *def_id, field: f as u32 };
                    let b = b.proj_and_reduce(proj);
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
            .map(|kind| {
                let (sort, _, kind) = kind.expect_refine();
                Expr::fvar(infcx.define_bound_reft_var(sort, kind))
            })
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
        if let BaseTy::Coroutine(def_id, resume_ty, upvar_tys, args) = bty {
            let obligs = mk_coroutine_obligations(
                infcx.genv,
                def_id,
                resume_ty,
                upvar_tys,
                &alias_ty.def_id,
                args.clone(),
            )?;
            self.obligations.extend(obligs);
        } else {
            let bounds = infcx.genv.item_bounds(alias_ty.def_id)?.instantiate(
                infcx.tcx(),
                &alias_ty.args,
                &alias_ty.refine_args,
            );
            for clause in &bounds {
                if !clause.kind().vars().is_empty() {
                    Err(query_bug!("handle_opaque_types: clause with bound vars: `{clause:?}`"))?;
                }
                if let rty::ClauseKind::Projection(pred) = clause.kind_skipping_binder() {
                    let alias_ty = pred.projection_ty.with_self_ty(bty.to_subset_ty_ctor());
                    let ty1 = BaseTy::Alias(AliasKind::Projection, alias_ty)
                        .to_ty()
                        .deeply_normalize(&mut infcx.at(self.span))?;
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
    args: flux_rustc_bridge::ty::GenericArgs,
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
                    args,
                }
            })]);
        }
    }
    bug!("no projection predicate")
}

#[derive(Debug)]
pub enum InferErr {
    UnsolvedEvar(EVid),
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
            w!(cx, f, "{:?} at {:?}", ^self.reason, self.src_span)?;
            if let Some(dst_span) = self.dst_span {
                w!(cx, f, " ({:?})", ^dst_span)?;
            }
            Ok(())
        }
    }

    impl_debug_with_default_cx!(Tag);
}
