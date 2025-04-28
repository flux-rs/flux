use std::{collections::hash_map::Entry, iter};

use flux_common::{bug, dbg, index::IndexVec, iter::IterExt, tracked_span_bug};
use flux_config::{self as config, InferOpts};
use flux_infer::{
    infer::{
        ConstrReason, GlobalEnvExt as _, InferCtxt, InferCtxtRoot, InferResult, SubtypeReason,
    },
    projections::NormalizeExt as _,
    refine_tree::{Marker, RefineCtxtTrace},
};
use flux_middle::{
    global_env::GlobalEnv,
    queries::{QueryResult, try_query},
    query_bug,
    rty::{
        self, AdtDef, BaseTy, Binder, Bool, Clause, CoroutineObligPredicate, EarlyBinder, Expr,
        FnOutput, FnTraitPredicate, GenericArg, GenericArgsExt as _, Int, IntTy, Mutability, Path,
        PolyFnSig, PtrKind, RefineArgs, RefineArgsExt,
        Region::ReStatic,
        Ty, TyKind, Uint, UintTy, VariantIdx,
        fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
        refining::{Refine, Refiner},
    },
};
use flux_rustc_bridge::{
    self,
    mir::{
        self, AggregateKind, AssertKind, BasicBlock, Body, BorrowKind, CastKind, Constant,
        Location, NonDivergingIntrinsic, Operand, Place, Rvalue, START_BLOCK, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{self, GenericArgsExt as _},
};
use itertools::{Itertools, izip};
use rustc_data_structures::{graph::dominators::Dominators, unord::UnordMap};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    LangItem,
    def_id::{DefId, LocalDefId},
};
use rustc_index::bit_set::DenseBitSet;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::SwitchTargets,
    ty::{TyCtxt, TypeSuperVisitable as _, TypeVisitable as _, TypingMode},
};
use rustc_span::{Span, sym};

use self::errors::{CheckerError, ResultExt};
use crate::{
    ghost_statements::{GhostStatement, GhostStatements, Point},
    primops,
    queue::WorkQueue,
    type_env::{
        BasicBlockEnv, BasicBlockEnvShape, PtrToRefBound, SpanTrace, TypeEnv, TypeEnvTrace,
    },
};

type Result<T = ()> = std::result::Result<T, CheckerError>;

pub(crate) struct Checker<'ck, 'genv, 'tcx, M> {
    genv: GlobalEnv<'genv, 'tcx>,
    /// [`LocalDefId`] of the function-like item being checked.
    def_id: LocalDefId,
    inherited: Inherited<'ck, M>,
    body: &'ck Body<'tcx>,
    /// The type used for the `resume` argument if we are checking a generator.
    resume_ty: Option<Ty>,
    output: Binder<FnOutput>,
    /// A marker to the node in the refinement tree at the end of the basic block after applying
    /// the effects of the terminator.
    markers: IndexVec<BasicBlock, Option<Marker>>,
    visited: DenseBitSet<BasicBlock>,
    queue: WorkQueue<'ck>,
    default_refiner: Refiner<'genv, 'tcx>,
}

/// Fields shared by the top-level function and its nested closure/generators
struct Inherited<'ck, M> {
    /// [`Expr`]s used to instantiate the early bound refinement parameters of the top-level function
    /// signature
    ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
    mode: &'ck mut M,
}

impl<'ck, M: Mode> Inherited<'ck, M> {
    fn new(
        mode: &'ck mut M,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
    ) -> Result<Self> {
        Ok(Self { ghost_stmts, mode })
    }

    fn reborrow(&mut self) -> Inherited<M> {
        Inherited { ghost_stmts: self.ghost_stmts, mode: &mut *self.mode }
    }
}

pub(crate) trait Mode: Sized {
    const NAME: &str;

    fn enter_basic_block<'ck, 'genv, 'tcx>(
        ck: &mut Checker<'ck, 'genv, 'tcx, Self>,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        bb: BasicBlock,
    ) -> TypeEnv<'ck>;

    fn check_goto_join_point<'genv, 'tcx>(
        ck: &mut Checker<'_, 'genv, 'tcx, Self>,
        infcx: InferCtxt<'_, 'genv, 'tcx>,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool>;

    fn clear(ck: &mut Checker<Self>, bb: BasicBlock);
}

pub(crate) struct ShapeMode {
    bb_envs: FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnvShape>>,
}

pub(crate) struct RefineMode {
    bb_envs: FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnv>>,
}

/// The result of running the shape phase.
pub(crate) struct ShapeResult(FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnvShape>>);

/// A `Guard` describes extra "control" information that holds at the start of a successor basic block
#[derive(Debug)]
enum Guard {
    /// No extra information holds, e.g., for a plain goto.
    None,
    /// A predicate that can be assumed, e.g., in the branches of an if-then-else.
    Pred(Expr),
    /// The corresponding place was found to be of a particular variant.
    Match(Place, VariantIdx),
}

impl<'ck, 'genv, 'tcx> Checker<'ck, 'genv, 'tcx, ShapeMode> {
    pub(crate) fn run_in_shape_mode(
        genv: GlobalEnv<'genv, 'tcx>,
        local_id: LocalDefId,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
        opts: InferOpts,
    ) -> Result<ShapeResult> {
        let def_id = local_id.to_def_id();
        dbg::shape_mode_span!(genv.tcx(), local_id).in_scope(|| {
            let span = genv.tcx().def_span(local_id);
            let mut mode = ShapeMode { bb_envs: FxHashMap::default() };

            let body = genv.mir(local_id).with_span(span)?;

            // In shape mode we don't care about kvars
            let mut root_ctxt = try_query(|| {
                genv.infcx_root(&body.infcx, opts)
                    .with_dummy_kvars()
                    .identity_for_item(def_id)?
                    .build()
            })
            .with_span(span)?;

            let inherited = Inherited::new(&mut mode, ghost_stmts)?;

            let infcx = root_ctxt.infcx(def_id, &body.infcx);
            let poly_sig = genv
                .fn_sig(local_id)
                .with_span(span)?
                .instantiate_identity();
            Checker::run(infcx, local_id, inherited, poly_sig)?;

            Ok(ShapeResult(mode.bb_envs))
        })
    }
}

impl<'ck, 'genv, 'tcx> Checker<'ck, 'genv, 'tcx, RefineMode> {
    pub(crate) fn run_in_refine_mode(
        genv: GlobalEnv<'genv, 'tcx>,
        local_id: LocalDefId,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
        bb_env_shapes: ShapeResult,
        opts: InferOpts,
    ) -> Result<InferCtxtRoot<'genv, 'tcx>> {
        let def_id = local_id.to_def_id();
        let span = genv.tcx().def_span(def_id);

        let body = genv.mir(local_id).with_span(span)?;
        let mut root_ctxt = try_query(|| {
            genv.infcx_root(&body.infcx, opts)
                .identity_for_item(def_id)?
                .build()
        })
        .with_span(span)?;
        let bb_envs = bb_env_shapes.into_bb_envs(&mut root_ctxt);

        dbg::refine_mode_span!(genv.tcx(), def_id, bb_envs).in_scope(|| {
            // Check the body of the function def_id against its signature
            let mut mode = RefineMode { bb_envs };
            let inherited = Inherited::new(&mut mode, ghost_stmts)?;
            let infcx = root_ctxt.infcx(def_id, &body.infcx);
            let poly_sig = genv.fn_sig(def_id).with_span(span)?.instantiate_identity();
            Checker::run(infcx, local_id, inherited, poly_sig)?;

            Ok(root_ctxt)
        })
    }
}

/// The function `check_fn_subtyping` does a function subtyping check between
/// the sub-type (T_f) corresponding to the type of `def_id` @ `args` and the
/// super-type (T_g) corresponding to the `oblig_sig`. This subtyping is handled
/// as akin to the code
///
///   T_f := (S1,...,Sn) -> S
///   T_g := (T1,...,Tn) -> T
///   T_f <: T_g
///
///  fn g(x1:T1,...,xn:Tn) -> T {
///      f(x1,...,xn)
///  }
fn check_fn_subtyping(
    infcx: &mut InferCtxt,
    def_id: &DefId,
    sub_sig: EarlyBinder<rty::PolyFnSig>,
    sub_args: &[GenericArg],
    super_sig: &rty::PolyFnSig,
    span: Span,
) -> InferResult {
    let mut infcx = infcx.branch();
    let mut infcx = infcx.at(span);
    let tcx = infcx.genv.tcx();

    let super_sig = super_sig
        .replace_bound_vars(|_| rty::ReErased, |sort, _| Expr::fvar(infcx.define_var(sort)))
        .normalize_projections(&mut infcx)?;

    // 1. Unpack `T_g` input types
    let actuals = super_sig
        .inputs()
        .iter()
        .map(|ty| infcx.unpack(ty))
        .collect_vec();

    let mut env = TypeEnv::empty();
    let actuals = unfold_local_ptrs(&mut infcx, &mut env, &sub_sig, &actuals)?;
    let actuals = infer_under_mut_ref_hack(&mut infcx, &actuals[..], sub_sig.as_ref());

    let output = infcx.ensure_resolved_evars(|infcx| {
        // 2. Fresh names for `T_f` refine-params / Instantiate fn_def_sig and normalize it
        let refine_args = infcx.instantiate_refine_args(*def_id, sub_args)?;
        let sub_sig = sub_sig.instantiate(tcx, sub_args, &refine_args);
        let sub_sig = sub_sig
            .replace_bound_vars(|_| rty::ReErased, |sort, mode| infcx.fresh_infer_var(sort, mode))
            .normalize_projections(infcx)?;

        // 3. INPUT subtyping (g-input <: f-input)
        for requires in super_sig.requires() {
            infcx.assume_pred(requires);
        }
        for (actual, formal) in iter::zip(actuals, sub_sig.inputs()) {
            let reason = ConstrReason::Subtype(SubtypeReason::Input);
            infcx.subtyping_with_env(&mut env, &actual, formal, reason)?;
        }
        // we check the requires AFTER the actual-formal subtyping as the above may unfold stuff in
        // the actuals
        for requires in sub_sig.requires() {
            let reason = ConstrReason::Subtype(SubtypeReason::Requires);
            infcx.check_pred(requires, reason);
        }

        Ok(sub_sig.output())
    })?;

    let output = infcx
        .fully_resolve_evars(&output)
        .replace_bound_refts_with(|sort, _, _| Expr::fvar(infcx.define_var(sort)));

    // 4. OUTPUT subtyping (f_out <: g_out)
    infcx.ensure_resolved_evars(|infcx| {
        let super_output = super_sig
            .output()
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));
        let reason = ConstrReason::Subtype(SubtypeReason::Output);
        infcx.subtyping(&output.ret, &super_output.ret, reason)?;

        // 6. Update state with Output "ensures" and check super ensures
        env.assume_ensures(infcx, &output.ensures);
        fold_local_ptrs(infcx, &mut env, span)?;
        env.check_ensures(
            infcx,
            &super_output.ensures,
            ConstrReason::Subtype(SubtypeReason::Ensures),
        )
    })
}

/// Trait subtyping check, which makes sure that the type for an impl method (def_id)
/// is a subtype of the corresponding trait method.
pub(crate) fn trait_impl_subtyping<'genv, 'tcx>(
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: LocalDefId,
    opts: InferOpts,
    span: Span,
) -> InferResult<Option<InferCtxtRoot<'genv, 'tcx>>> {
    let tcx = genv.tcx();

    // Skip the check if this is not an impl method
    let Some((impl_trait_ref, trait_method_id)) = find_trait_item(genv, def_id)? else {
        return Ok(None);
    };
    let impl_method_id = def_id.to_def_id();
    // Skip the check if either the trait-method or the impl-method are marked as `trusted_impl`
    if genv.has_trusted_impl(trait_method_id) || genv.has_trusted_impl(impl_method_id) {
        return Ok(None);
    }

    let impl_id = tcx.impl_of_method(impl_method_id).unwrap();
    let impl_method_args = GenericArg::identity_for_item(genv, impl_method_id)?;
    let trait_method_args = impl_method_args.rebase_onto(&tcx, impl_id, &impl_trait_ref.args);
    let trait_refine_args = RefineArgs::identity_for_item(genv, trait_method_id)?;

    let rustc_infcx = genv
        .tcx()
        .infer_ctxt()
        .build(TypingMode::non_body_analysis());

    let mut root_ctxt = genv
        .infcx_root(&rustc_infcx, opts)
        .with_const_generics(impl_id)?
        .with_refinement_generics(trait_method_id, &trait_method_args)?
        .build()?;

    let mut infcx = root_ctxt.infcx(impl_method_id, &rustc_infcx);

    let trait_fn_sig =
        genv.fn_sig(trait_method_id)?
            .instantiate(tcx, &trait_method_args, &trait_refine_args);
    let impl_sig = genv.fn_sig(impl_method_id)?;

    check_fn_subtyping(
        &mut infcx,
        &impl_method_id,
        impl_sig,
        &impl_method_args,
        &trait_fn_sig,
        span,
    )?;
    Ok(Some(root_ctxt))
}

fn find_trait_item(
    genv: GlobalEnv<'_, '_>,
    def_id: LocalDefId,
) -> QueryResult<Option<(rty::TraitRef, DefId)>> {
    let tcx = genv.tcx();
    let def_id = def_id.to_def_id();
    if let Some(impl_id) = tcx.impl_of_method(def_id)
        && let Some(impl_trait_ref) = genv.impl_trait_ref(impl_id)?
    {
        let impl_trait_ref = impl_trait_ref.instantiate_identity();
        let trait_item_id = tcx.associated_item(def_id).trait_item_def_id.unwrap();
        return Ok(Some((impl_trait_ref, trait_item_id)));
    }
    Ok(None)
}

/// Temporarily (around a function call) convert an `&mut` to an `&strg` to allow for the call to be
/// checked. This is done by unfolding the `&mut` into a local pointer at the call-site and then
/// folding the pointer back into the `&mut` upon return.
/// See also [`fold_local_ptrs`].
///
/// ```text
///             unpack(T) = T'
/// ---------------------------------------[local-unfold]
/// Γ ; &mut T => Γ, l:[<: T] T' ; ptr(l)
/// ```
fn unfold_local_ptrs(
    infcx: &mut InferCtxt,
    env: &mut TypeEnv,
    fn_sig: &EarlyBinder<PolyFnSig>,
    actuals: &[Ty],
) -> InferResult<Vec<Ty>> {
    // We *only* need to know whether each input is a &strg or not
    let fn_sig = fn_sig.skip_binder_ref().skip_binder_ref();
    let mut tys = vec![];
    for (actual, input) in izip!(actuals, fn_sig.inputs()) {
        let actual = if let (
            TyKind::Indexed(BaseTy::Ref(re, bound, Mutability::Mut), _),
            TyKind::StrgRef(_, _, _),
        ) = (actual.kind(), input.kind())
        {
            let loc = env.unfold_local_ptr(infcx, bound)?;
            let path1 = Path::new(loc, rty::List::empty());
            Ty::ptr(PtrKind::Mut(*re), path1)
        } else {
            actual.clone()
        };
        tys.push(actual);
    }
    Ok(tys)
}

/// Fold local pointers implements roughly a rule like the following (for all local pointers)
/// that converts the local pointers created via [`unfold_local_ptrs`] back into `&mut`.
///
/// ```text
///       T1 <: T2
/// --------------------- [local-fold]
/// Γ, l:[<: T2] T1 => Γ
/// ```
fn fold_local_ptrs(infcx: &mut InferCtxt, env: &mut TypeEnv, span: Span) -> InferResult {
    let mut at = infcx.at(span);
    env.fold_local_ptrs(&mut at)
}

impl<'ck, 'genv, 'tcx, M: Mode> Checker<'ck, 'genv, 'tcx, M> {
    fn run(
        mut infcx: InferCtxt<'_, 'genv, 'tcx>,
        def_id: LocalDefId,
        inherited: Inherited<'ck, M>,
        poly_sig: PolyFnSig,
    ) -> Result {
        let genv = infcx.genv;
        let span = genv.tcx().def_span(def_id);

        let body = genv.mir(def_id).with_span(span)?;

        let fn_sig = poly_sig
            .replace_bound_vars(|_| rty::ReErased, |sort, _| Expr::fvar(infcx.define_var(sort)))
            .normalize_projections(&mut infcx)
            .with_span(span)?;

        let mut env = TypeEnv::new(&mut infcx, &body, &fn_sig);

        // (NOTE:YIELD) per https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html#variant.Yield
        //   "execution of THIS function continues at the `resume` basic block, with THE SECOND ARGUMENT WRITTEN
        //    to the `resume_arg` place..."
        let resume_ty = if genv.tcx().is_coroutine(def_id.to_def_id()) {
            Some(fn_sig.inputs()[1].clone())
        } else {
            None
        };
        let mut ck = Checker {
            def_id,
            genv,
            inherited,
            body: &body,
            resume_ty,
            visited: DenseBitSet::new_empty(body.basic_blocks.len()),
            output: fn_sig.output().clone(),
            markers: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            queue: WorkQueue::empty(body.basic_blocks.len(), &body.dominator_order_rank),
            default_refiner: Refiner::default_for_item(genv, def_id.to_def_id()).with_span(span)?,
        };
        ck.check_ghost_statements_at(&mut infcx, &mut env, Point::FunEntry, body.span())?;

        ck.check_goto(infcx.branch(), env, body.span(), START_BLOCK)?;

        while let Some(bb) = ck.queue.pop() {
            let visited = ck.visited.contains(bb);

            if visited {
                M::clear(&mut ck, bb);
            }

            let marker = ck.marker_at_dominator(bb);
            let mut infcx = infcx.move_to(marker, visited);
            let mut env = M::enter_basic_block(&mut ck, &mut infcx, bb);
            env.unpack(&mut infcx);
            ck.check_basic_block(infcx, env, bb)?;
        }

        Ok(())
    }

    fn check_basic_block(
        &mut self,
        mut infcx: InferCtxt<'_, 'genv, 'tcx>,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result {
        dbg::basic_block_start!(bb, infcx, env);

        self.visited.insert(bb);
        let data = &self.body.basic_blocks[bb];
        let mut last_stmt_span = None;
        let mut location = Location { block: bb, statement_index: 0 };
        for stmt in &data.statements {
            let span = stmt.source_info.span;
            self.check_ghost_statements_at(
                &mut infcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;
            bug::track_span(span, || {
                dbg::statement!("start", stmt, &infcx, &env, span, &self);
                self.check_statement(&mut infcx, &mut env, stmt)?;
                dbg::statement!("end", stmt, &infcx, &env, span, &self);
                Ok(())
            })?;
            if !stmt.is_nop() {
                last_stmt_span = Some(span);
            }
            location = location.successor_within_block();
        }

        if let Some(terminator) = &data.terminator {
            let span = terminator.source_info.span;
            self.check_ghost_statements_at(
                &mut infcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;

            bug::track_span(span, || {
                dbg::terminator!("start", terminator, infcx, env);

                let successors =
                    self.check_terminator(&mut infcx, &mut env, terminator, last_stmt_span)?;
                dbg::terminator!("end", terminator, infcx, env);

                self.markers[bb] = Some(infcx.marker());
                let term_span = last_stmt_span.unwrap_or(span);
                self.check_successors(infcx, env, bb, term_span, successors)
            })?;
        }
        Ok(())
    }

    fn check_assign_ty(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut TypeEnv,
        place: &Place,
        ty: Ty,
        span: Span,
    ) -> InferResult {
        let ty = infcx.hoister(true).hoist(&ty);
        env.assign(&mut infcx.at(span), place, ty)
    }

    fn check_statement(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt: &Statement,
    ) -> Result {
        let stmt_span = stmt.source_info.span;
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(infcx, env, stmt_span, rvalue)?;
                self.check_assign_ty(infcx, env, place, ty, stmt_span)
                    .with_span(stmt_span)?;
            }
            StatementKind::SetDiscriminant { .. } => {
                // TODO(nilehmann) double check here that the place is unfolded to
                // the correct variant. This should be guaranteed by rustc
            }
            StatementKind::FakeRead(_) => {
                // TODO(nilehmann) fake reads should be folding points
            }
            StatementKind::AscribeUserType(_, _) => {
                // User ascriptions affect nll, but no refinement type checking.
                // Maybe we can use this to associate refinement type to locals.
            }
            StatementKind::PlaceMention(_) => {
                // Place mentions are a no-op used to detect uses of unsafe that would
                // otherwise be optimized away.
            }
            StatementKind::Nop => {}
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                // Currently, we only have the `assume` intrinsic, which if we're to trust rustc should be a NOP.
                // TODO: There may be a use-case to actually "assume" the bool index associated with the operand,
                // i.e. to strengthen the `rcx` / `env` with the assumption that the bool-index is in fact `true`...
                let _ = self
                    .check_operand(infcx, env, stmt_span, op)
                    .with_span(stmt_span)?;
            }
        }
        Ok(())
    }

    fn is_exit_block(&self, bb: BasicBlock) -> bool {
        let data = &self.body.basic_blocks[bb];
        let is_no_op = data.statements.iter().all(Statement::is_nop);
        let is_ret = match &data.terminator {
            None => false,
            Some(term) => term.is_return(),
        };
        is_no_op && is_ret
    }

    /// For `check_terminator`, the output `Vec<BasicBlock, Guard>` denotes,
    /// - `BasicBlock` "successors" of the current terminator, and
    /// - `Guard` are extra control information from, e.g. the `SwitchInt` (or `Assert`)
    ///    you can assume when checking the corresponding successor.
    fn check_terminator(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        terminator: &Terminator<'tcx>,
        last_stmt_span: Option<Span>,
    ) -> Result<Vec<(BasicBlock, Guard)>> {
        let source_info = terminator.source_info;
        let terminator_span = source_info.span;
        match &terminator.kind {
            TerminatorKind::Return => {
                self.check_ret(infcx, env, last_stmt_span.unwrap_or(terminator_span))?;
                Ok(vec![])
            }
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::CoroutineDrop => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::Yield { resume, resume_arg, .. } => {
                if let Some(resume_ty) = self.resume_ty.clone() {
                    self.check_assign_ty(infcx, env, resume_arg, resume_ty, terminator_span)
                        .with_span(terminator_span)?;
                } else {
                    bug!("yield in non-generator function");
                }
                Ok(vec![(*resume, Guard::None)])
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self
                    .check_operand(infcx, env, terminator_span, discr)
                    .with_span(terminator_span)?;
                if discr_ty.is_integral() || discr_ty.is_bool() || discr_ty.is_char() {
                    Ok(Self::check_if(&discr_ty, targets))
                } else {
                    Ok(Self::check_match(&discr_ty, targets))
                }
            }
            TerminatorKind::Call { kind, args, destination, target, .. } => {
                let actuals = self
                    .check_operands(infcx, env, terminator_span, args)
                    .with_span(terminator_span)?;
                let ret = match kind {
                    mir::CallKind::FnDef { resolved_id, resolved_args, .. } => {
                        let fn_sig = self.genv.fn_sig(*resolved_id).with_span(terminator_span)?;

                        let generic_args = instantiate_args_for_fun_call(
                            self.genv,
                            self.def_id.to_def_id(),
                            *resolved_id,
                            &resolved_args.lowered,
                        )
                        .with_span(terminator_span)?;
                        self.check_call(
                            infcx,
                            env,
                            terminator_span,
                            Some(*resolved_id),
                            fn_sig,
                            &generic_args,
                            &actuals,
                        )?
                    }
                    mir::CallKind::FnPtr { operand, .. } => {
                        let ty = self
                            .check_operand(infcx, env, terminator_span, operand)
                            .with_span(terminator_span)?;
                        if let TyKind::Indexed(BaseTy::FnPtr(fn_sig), _) = infcx.unpack(&ty).kind()
                        {
                            self.check_call(
                                infcx,
                                env,
                                terminator_span,
                                None,
                                EarlyBinder(fn_sig.clone()),
                                &[],
                                &actuals,
                            )?
                        } else {
                            bug!("TODO: fnptr call {ty:?}")
                        }
                    }
                };

                let ret = infcx.unpack(&ret);
                infcx.assume_invariants(&ret);

                env.assign(&mut infcx.at(terminator_span), destination, ret)
                    .with_span(terminator_span)?;

                if let Some(target) = target {
                    Ok(vec![(*target, Guard::None)])
                } else {
                    Ok(vec![])
                }
            }
            TerminatorKind::Assert { cond, expected, target, msg } => {
                Ok(vec![(
                    *target,
                    self.check_assert(infcx, env, terminator_span, cond, *expected, msg)
                        .with_span(terminator_span)?,
                )])
            }
            TerminatorKind::Drop { place, target, .. } => {
                let _ = env.move_place(&mut infcx.at(terminator_span), place);
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::FalseEdge { real_target, .. } => Ok(vec![(*real_target, Guard::None)]),
            TerminatorKind::FalseUnwind { real_target, .. } => {
                Ok(vec![(*real_target, Guard::None)])
            }
            TerminatorKind::UnwindResume => bug!("TODO: implement checking of cleanup code"),
        }
    }

    fn check_ret(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        span: Span,
    ) -> Result {
        let obligations = infcx
            .at(span)
            .ensure_resolved_evars(|infcx| {
                let ret_place_ty = env.lookup_place(infcx, Place::RETURN)?;
                let output = self
                    .output
                    .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));
                let obligations = infcx.subtyping(&ret_place_ty, &output.ret, ConstrReason::Ret)?;

                env.check_ensures(infcx, &output.ensures, ConstrReason::Ret)?;

                Ok(obligations)
            })
            .with_span(span)?;

        self.check_coroutine_obligations(infcx, obligations)
    }

    #[expect(clippy::too_many_arguments)]
    fn check_call(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        span: Span,
        callee_def_id: Option<DefId>,
        fn_sig: EarlyBinder<PolyFnSig>,
        generic_args: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<Ty> {
        let genv = self.genv;
        let tcx = genv.tcx();

        let actuals = unfold_local_ptrs(infcx, env, &fn_sig, actuals).with_span(span)?;
        let actuals = infer_under_mut_ref_hack(infcx, &actuals, fn_sig.as_ref());
        infcx.push_evar_scope();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        // Generate fresh inference variables for refinement arguments
        let refine_args = match callee_def_id {
            Some(callee_def_id) => {
                infcx
                    .instantiate_refine_args(callee_def_id, &generic_args)
                    .with_span(span)?
            }
            None => rty::List::empty(),
        };

        let clauses = match callee_def_id {
            Some(callee_def_id) => {
                genv.predicates_of(callee_def_id)
                    .with_span(span)?
                    .predicates()
                    .instantiate(tcx, &generic_args, &refine_args)
            }
            None => crate::rty::List::empty(),
        };

        let (clauses, fn_clauses) = Clause::split_off_fn_trait_clauses(self.genv, &clauses);
        infcx
            .at(span)
            .check_non_closure_clauses(&clauses, ConstrReason::Call)
            .with_span(span)?;
        self.check_closure_clauses(infcx, &fn_clauses, span)?;

        // Instantiate function signature and normalize it
        let fn_sig = fn_sig
            .instantiate(tcx, &generic_args, &refine_args)
            .replace_bound_vars(|_| rty::ReErased, |sort, mode| infcx.fresh_infer_var(sort, mode))
            .normalize_projections(infcx)
            .with_span(span)?;

        let mut at = infcx.at(span);

        // Check requires predicates
        for requires in fn_sig.requires() {
            at.check_pred(requires, ConstrReason::Call);
        }

        // Check arguments
        for (actual, formal) in iter::zip(actuals, fn_sig.inputs()) {
            at.subtyping_with_env(env, &actual, formal, ConstrReason::Call)
                .with_span(span)?;
        }

        infcx.pop_evar_scope().with_span(span)?;
        env.fully_resolve_evars(infcx);

        let output = infcx
            .fully_resolve_evars(&fn_sig.output)
            .replace_bound_refts_with(|sort, _, _| Expr::fvar(infcx.define_var(sort)));

        env.assume_ensures(infcx, &output.ensures);
        fold_local_ptrs(infcx, env, span).with_span(span)?;

        Ok(output.ret)
    }

    fn check_coroutine_obligations(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        obligs: Vec<Binder<CoroutineObligPredicate>>,
    ) -> Result {
        for oblig in obligs {
            // FIXME(nilehmann) we shouldn't be skipping this binder
            let oblig = oblig.skip_binder();

            #[expect(clippy::disallowed_methods, reason = "coroutines cannot be extern speced")]
            let def_id = oblig.def_id.expect_local();
            let span = self.genv.tcx().def_span(def_id);
            let body = self.genv.mir(def_id).with_span(span)?;
            Checker::run(
                infcx.change_item(def_id, &body.infcx),
                def_id,
                self.inherited.reborrow(),
                oblig.to_poly_fn_sig(),
            )?;
        }
        Ok(())
    }

    fn check_fn_trait_clause(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        fn_trait_pred: &FnTraitPredicate,
        span: Span,
    ) -> Result {
        let self_ty = fn_trait_pred.self_ty.as_bty_skipping_existentials();
        match self_ty {
            Some(BaseTy::Closure(closure_id, tys, args)) => {
                #[expect(clippy::disallowed_methods, reason = "closures cannot be extern speced")]
                let local_closure_id = closure_id.expect_local();
                let span = self.genv.tcx().def_span(local_closure_id);
                let body = self.genv.mir(local_closure_id).with_span(span)?;
                Checker::run(
                    infcx.change_item(local_closure_id, &body.infcx),
                    local_closure_id,
                    self.inherited.reborrow(),
                    fn_trait_pred.to_closure_sig(*closure_id, tys.clone(), args),
                )?;
            }
            Some(BaseTy::FnDef(def_id, args)) => {
                // Generates "function subtyping" obligations between the (super-type) `oblig_sig` in the `fn_trait_pred`
                // and the (sub-type) corresponding to the signature of `def_id + args`.
                // See `tests/neg/surface/fndef00.rs`
                let sub_sig = self.genv.fn_sig(def_id).with_span(span)?;
                let oblig_sig = fn_trait_pred.fndef_poly_sig();
                check_fn_subtyping(infcx, def_id, sub_sig, args, &oblig_sig, span)
                    .with_span(span)?;
            }
            _ => {
                // TODO: When we allow refining closure/fn at the surface level, we would need to do some function subtyping here,
                // but for now, we can skip as all the relevant types are unrefined.
                // See issue-767.rs
            }
        }
        Ok(())
    }

    fn check_closure_clauses(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        clauses: &[Binder<FnTraitPredicate>],
        span: Span,
    ) -> Result {
        for clause in clauses {
            // FIXME(nilehmann) we shouldn't be skipping this binder
            let clause = clause.skip_binder_ref();

            self.check_fn_trait_clause(infcx, clause, span)?;
        }
        Ok(())
    }

    fn check_assert(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut TypeEnv,
        terminator_span: Span,
        cond: &Operand,
        expected: bool,
        msg: &AssertKind,
    ) -> InferResult<Guard> {
        let ty = self.check_operand(infcx, env, terminator_span, cond)?;
        let TyKind::Indexed(BaseTy::Bool, idx) = ty.kind() else {
            tracked_span_bug!("unexpected ty `{ty:?}`");
        };
        let pred = if expected { idx.clone() } else { idx.not() };

        let msg = match msg {
            AssertKind::DivisionByZero => "possible division by zero",
            AssertKind::BoundsCheck => "possible out-of-bounds access",
            AssertKind::RemainderByZero => "possible remainder with a divisor of zero",
            AssertKind::Overflow(mir::BinOp::Div) => "possible division with overflow",
            AssertKind::Overflow(mir::BinOp::Rem) => "possible reminder with overflow",
            AssertKind::Overflow(_) => return Ok(Guard::Pred(pred)),
        };
        infcx
            .at(terminator_span)
            .check_pred(&pred, ConstrReason::Assert(msg));
        Ok(Guard::Pred(pred))
    }

    /// Checks conditional branching as in a `match` statement. [`SwitchTargets`](https://doc.rust-lang.org/nightly/nightly-rustc/stable_mir/mir/struct.SwitchTargets.html) contains a list of branches - the exact bit value which is being compared and the block to jump to. Using the conditionals, each branch can be checked using the new control flow information.
    /// See <https://github.com/flux-rs/flux/pull/840#discussion_r1786543174>
    fn check_if(discr_ty: &Ty, targets: &SwitchTargets) -> Vec<(BasicBlock, Guard)> {
        let mk = |bits| {
            match discr_ty.kind() {
                TyKind::Indexed(BaseTy::Bool, idx) => {
                    if bits == 0 {
                        idx.not()
                    } else {
                        idx.clone()
                    }
                }
                TyKind::Indexed(bty @ (BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Char), idx) => {
                    Expr::eq(idx.clone(), Expr::from_bits(bty, bits))
                }
                _ => tracked_span_bug!("unexpected discr_ty {:?}", discr_ty),
            }
        };

        let mut successors = vec![];

        for (bits, bb) in targets.iter() {
            successors.push((bb, Guard::Pred(mk(bits))));
        }
        let otherwise = Expr::and_from_iter(targets.iter().map(|(bits, _)| mk(bits).not()));
        successors.push((targets.otherwise(), Guard::Pred(otherwise)));

        successors
    }

    fn check_match(discr_ty: &Ty, targets: &SwitchTargets) -> Vec<(BasicBlock, Guard)> {
        let (adt_def, place) = discr_ty.expect_discr();

        let mut successors = vec![];
        let mut remaining: FxHashMap<u128, VariantIdx> = adt_def
            .discriminants()
            .map(|(idx, discr)| (discr, idx))
            .collect();
        for (bits, bb) in targets.iter() {
            let variant_idx = remaining
                .remove(&bits)
                .expect("value doesn't correspond to any variant");
            successors.push((bb, Guard::Match(place.clone(), variant_idx)));
        }

        if remaining.len() == 1 {
            let (_, variant_idx) = remaining
                .into_iter()
                .next()
                .unwrap_or_else(|| tracked_span_bug!());
            successors.push((targets.otherwise(), Guard::Match(place.clone(), variant_idx)));
        } else {
            successors.push((targets.otherwise(), Guard::None));
        }

        successors
    }

    fn check_successors(
        &mut self,
        mut infcx: InferCtxt<'_, 'genv, 'tcx>,
        env: TypeEnv,
        from: BasicBlock,
        terminator_span: Span,
        successors: Vec<(BasicBlock, Guard)>,
    ) -> Result {
        for (target, guard) in successors {
            let mut infcx = infcx.branch();
            let mut env = env.clone();
            match guard {
                Guard::None => {}
                Guard::Pred(expr) => {
                    infcx.assume_pred(&expr);
                }
                Guard::Match(place, variant_idx) => {
                    env.downcast(&mut infcx.at(terminator_span), &place, variant_idx)
                        .with_span(terminator_span)?;
                }
            }
            self.check_ghost_statements_at(
                &mut infcx,
                &mut env,
                Point::Edge(from, target),
                terminator_span,
            )?;
            self.check_goto(infcx, env, terminator_span, target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        mut infcx: InferCtxt<'_, 'genv, 'tcx>,
        mut env: TypeEnv,
        span: Span,
        target: BasicBlock,
    ) -> Result {
        if self.is_exit_block(target) {
            let location = self.body.terminator_loc(target);
            self.check_ghost_statements_at(
                &mut infcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;
            self.check_ret(&mut infcx, &mut env, span)
        } else if self.body.is_join_point(target) {
            if M::check_goto_join_point(self, infcx, env, span, target)? {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.check_basic_block(infcx, env, target)
        }
    }

    fn check_rvalue(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt_span: Span,
        rvalue: &Rvalue,
    ) -> Result<Ty> {
        let genv = self.genv;
        match rvalue {
            Rvalue::Use(operand) => {
                self.check_operand(infcx, env, stmt_span, operand)
                    .with_span(stmt_span)
            }
            Rvalue::Repeat(operand, c) => {
                let ty = self
                    .check_operand(infcx, env, stmt_span, operand)
                    .with_span(stmt_span)?;
                Ok(Ty::array(ty, c.clone()))
            }
            Rvalue::Ref(r, BorrowKind::Mut { .. }, place) => {
                env.borrow(&mut infcx.at(stmt_span), *r, Mutability::Mut, place)
                    .with_span(stmt_span)
            }
            Rvalue::Ref(r, BorrowKind::Shared | BorrowKind::Fake(..), place) => {
                env.borrow(&mut infcx.at(stmt_span), *r, Mutability::Not, place)
                    .with_span(stmt_span)
            }
            Rvalue::RawPtr(mutbl, place) => {
                // ignore any refinements on the type stored at place
                let ty = self
                    .refine_default(&env.lookup_rust_ty(genv, place).with_span(stmt_span)?)
                    .with_span(stmt_span)?;
                Ok(BaseTy::RawPtr(ty, *mutbl).to_ty())
            }
            Rvalue::Len(place) => self.check_len(infcx, env, stmt_span, place),
            Rvalue::Cast(kind, op, to) => {
                let from = self
                    .check_operand(infcx, env, stmt_span, op)
                    .with_span(stmt_span)?;
                self.check_cast(infcx, env, stmt_span, *kind, &from, to)
                    .with_span(stmt_span)
            }
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(infcx, env, stmt_span, *bin_op, op1, op2)
                    .with_span(stmt_span)
            }
            Rvalue::NullaryOp(null_op, ty) => Ok(self.check_nullary_op(*null_op, ty)),
            Rvalue::UnaryOp(un_op, op) => {
                self.check_unary_op(infcx, env, stmt_span, *un_op, op)
                    .with_span(stmt_span)
            }
            Rvalue::Discriminant(place) => {
                let ty = env
                    .lookup_place(&mut infcx.at(stmt_span), place)
                    .with_span(stmt_span)?;
                // HACK(nilehmann, mut-ref-unfolding) place should be unfolded here.
                let (adt_def, ..) = ty
                    .as_bty_skipping_existentials()
                    .unwrap_or_else(|| tracked_span_bug!())
                    .expect_adt();
                Ok(Ty::discr(adt_def.clone(), place.clone()))
            }
            Rvalue::Aggregate(
                AggregateKind::Adt(def_id, variant_idx, args, _, field_idx),
                operands,
            ) => {
                let actuals = self
                    .check_operands(infcx, env, stmt_span, operands)
                    .with_span(stmt_span)?;
                let sig = genv
                    .variant_sig(*def_id, *variant_idx)
                    .with_span(stmt_span)?
                    .ok_or_else(|| CheckerError::opaque_struct(*def_id, stmt_span))?
                    .to_poly_fn_sig(*field_idx);

                let args =
                    instantiate_args_for_constructor(genv, self.def_id.to_def_id(), *def_id, args)
                        .with_span(stmt_span)?;
                self.check_call(infcx, env, stmt_span, Some(*def_id), sig, &args, &actuals)
            }
            Rvalue::Aggregate(AggregateKind::Array(arr_ty), operands) => {
                let args = self
                    .check_operands(infcx, env, stmt_span, operands)
                    .with_span(stmt_span)?;
                let arr_ty = self.refine_with_holes(arr_ty).with_span(stmt_span)?;
                self.check_mk_array(infcx, env, stmt_span, &args, arr_ty)
                    .with_span(stmt_span)
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                let tys = self
                    .check_operands(infcx, env, stmt_span, args)
                    .with_span(stmt_span)?;
                Ok(Ty::tuple(tys))
            }
            Rvalue::Aggregate(AggregateKind::Closure(did, args), operands) => {
                let upvar_tys = self
                    .check_operands(infcx, env, stmt_span, operands)
                    .with_span(stmt_span)?
                    .into_iter()
                    .map(|ty| {
                        if let TyKind::Ptr(PtrKind::Mut(re), path) = ty.kind() {
                            env.ptr_to_ref(
                                &mut infcx.at(stmt_span),
                                ConstrReason::Other,
                                *re,
                                path,
                                PtrToRefBound::Infer,
                            )
                        } else {
                            Ok(ty.clone())
                        }
                    })
                    .try_collect_vec()
                    .with_span(stmt_span)?;

                Ok(Ty::closure(*did, upvar_tys, args))
            }
            Rvalue::Aggregate(AggregateKind::Coroutine(did, args), ops) => {
                let args = args.as_coroutine();
                let resume_ty = self.refine_default(args.resume_ty()).with_span(stmt_span)?;
                let upvar_tys = self
                    .check_operands(infcx, env, stmt_span, ops)
                    .with_span(stmt_span)?;
                Ok(Ty::coroutine(*did, resume_ty, upvar_tys.into()))
            }
            Rvalue::ShallowInitBox(operand, _) => {
                self.check_operand(infcx, env, stmt_span, operand)
                    .with_span(stmt_span)?;
                Ty::mk_box_with_default_alloc(self.genv, Ty::uninit()).with_span(stmt_span)
            }
        }
    }

    fn check_len(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut TypeEnv,
        stmt_span: Span,
        place: &Place,
    ) -> Result<Ty> {
        let ty = env
            .lookup_place(&mut infcx.at(stmt_span), place)
            .with_span(stmt_span)?;

        let idx = match ty.kind() {
            TyKind::Indexed(BaseTy::Array(_, len), _) => Expr::from_const(self.genv.tcx(), len),
            TyKind::Indexed(BaseTy::Slice(_), idx) => idx.clone(),
            _ => tracked_span_bug!("expected array or slice type found `{ty:?}`"),
        };

        Ok(Ty::indexed(BaseTy::Uint(UintTy::Usize), idx))
    }

    fn check_binary_op(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut TypeEnv,
        stmt_span: Span,
        bin_op: mir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> InferResult<Ty> {
        let ty1 = self.check_operand(infcx, env, stmt_span, op1)?;
        let ty2 = self.check_operand(infcx, env, stmt_span, op2)?;

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                let rule =
                    primops::match_bin_op(bin_op, bty1, idx1, bty2, idx2, infcx.check_overflow);
                if let Some(pre) = rule.precondition {
                    infcx.at(stmt_span).check_pred(pre.pred, pre.reason);
                }

                Ok(rule.output_type)
            }
            _ => tracked_span_bug!("incompatible types: `{ty1:?}` `{ty2:?}`"),
        }
    }

    fn check_nullary_op(&self, null_op: mir::NullOp, _ty: &ty::Ty) -> Ty {
        match null_op {
            mir::NullOp::SizeOf | mir::NullOp::AlignOf => {
                // We could try to get the layout of type to index this with the actual value, but
                // this enough for now. Revisit if we ever need the precision.
                Ty::uint(UintTy::Usize)
            }
        }
    }

    fn check_unary_op(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt_span: Span,
        un_op: mir::UnOp,
        op: &Operand,
    ) -> InferResult<Ty> {
        let ty = self.check_operand(infcx, env, stmt_span, op)?;
        match ty.kind() {
            TyKind::Indexed(bty, idx) => {
                let rule = primops::match_un_op(un_op, bty, idx, infcx.check_overflow);
                if let Some(pre) = rule.precondition {
                    infcx.at(stmt_span).check_pred(pre.pred, pre.reason);
                }
                Ok(rule.output_type)
            }
            _ => tracked_span_bug!("invalid type for unary operator `{un_op:?}` `{ty:?}`"),
        }
    }

    fn check_mk_array(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt_span: Span,
        args: &[Ty],
        arr_ty: Ty,
    ) -> InferResult<Ty> {
        let arr_ty = infcx.ensure_resolved_evars(|infcx| {
            let arr_ty =
                arr_ty.replace_holes(|binders, kind| infcx.fresh_infer_var_for_hole(binders, kind));

            let (arr_ty, pred) = arr_ty.unconstr();
            let mut at = infcx.at(stmt_span);
            at.check_pred(&pred, ConstrReason::Other);
            for ty in args {
                at.subtyping_with_env(env, ty, &arr_ty, ConstrReason::Other)?;
            }
            Ok(arr_ty)
        })?;
        let arr_ty = infcx.fully_resolve_evars(&arr_ty);

        Ok(Ty::array(arr_ty, rty::Const::from_usize(self.genv.tcx(), args.len())))
    }

    fn check_cast(
        &self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt_span: Span,
        kind: CastKind,
        from: &Ty,
        to: &ty::Ty,
    ) -> InferResult<Ty> {
        use ty::TyKind as RustTy;
        let ty = match kind {
            CastKind::PointerExposeProvenance => {
                match to.kind() {
                    RustTy::Int(int_ty) => Ty::int(*int_ty),
                    RustTy::Uint(uint_ty) => Ty::uint(*uint_ty),
                    _ => tracked_span_bug!("unsupported PointerExposeProvenance cast"),
                }
            }
            CastKind::IntToInt => {
                match (from.kind(), to.kind()) {
                    (Bool!(idx), RustTy::Int(int_ty)) => bool_int_cast(idx, *int_ty),
                    (Bool!(idx), RustTy::Uint(uint_ty)) => bool_uint_cast(idx, *uint_ty),
                    (Int!(int_ty1, idx), RustTy::Int(int_ty2)) => {
                        int_int_cast(idx, *int_ty1, *int_ty2)
                    }
                    (Uint!(uint_ty1, idx), RustTy::Uint(uint_ty2)) => {
                        uint_uint_cast(idx, *uint_ty1, *uint_ty2)
                    }
                    (Uint!(uint_ty, idx), RustTy::Int(int_ty)) => {
                        uint_int_cast(idx, *uint_ty, *int_ty)
                    }
                    (Int!(_, _), RustTy::Uint(uint_ty)) => Ty::uint(*uint_ty),
                    (TyKind::Discr(adt_def, _), RustTy::Int(int_ty)) => {
                        Self::discr_to_int_cast(adt_def, BaseTy::Int(*int_ty))
                    }
                    (TyKind::Discr(adt_def, _place), RustTy::Uint(uint_ty)) => {
                        Self::discr_to_int_cast(adt_def, BaseTy::Uint(*uint_ty))
                    }
                    _ => {
                        tracked_span_bug!("invalid int to int cast {from:?} --> {to:?}")
                    }
                }
            }
            CastKind::PointerCoercion(mir::PointerCast::Unsize) => {
                self.check_unsize_cast(infcx, env, stmt_span, from, to)?
            }
            CastKind::FloatToInt
            | CastKind::IntToFloat
            | CastKind::PtrToPtr
            | CastKind::PointerCoercion(mir::PointerCast::MutToConstPointer)
            | CastKind::PointerCoercion(mir::PointerCast::ClosureFnPointer)
            | CastKind::PointerWithExposedProvenance => self.refine_default(to)?,
            CastKind::PointerCoercion(mir::PointerCast::ReifyFnPointer) => {
                let to = self.refine_default(to)?;
                if let TyKind::Indexed(rty::BaseTy::FnDef(def_id, args), _) = from.kind()
                    && let TyKind::Indexed(BaseTy::FnPtr(super_sig), _) = to.kind()
                {
                    let current_did = infcx.def_id;
                    let sub_sig = infcx.genv.fn_sig(*def_id)?;
                    // // TODO(RJ) dicey maneuver? assumes that sig_b is unrefined?
                    check_fn_subtyping(infcx, &current_did, sub_sig, args, super_sig, stmt_span)?;
                    to
                } else {
                    tracked_span_bug!("invalid cast from `{from:?}` to `{to:?}`")
                }
            }
        };
        Ok(ty)
    }

    fn discr_to_int_cast(adt_def: &AdtDef, bty: BaseTy) -> Ty {
        // TODO: This could be a giant disjunction, maybe better (if less precise) to use the interval?
        let vals = adt_def
            .discriminants()
            .map(|(_, idx)| Expr::eq(Expr::nu(), Expr::from_bits(&bty, idx)))
            .collect_vec();
        Ty::exists_with_constr(bty, Expr::or_from_iter(vals))
    }

    fn check_unsize_cast(
        &self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        span: Span,
        src: &Ty,
        dst: &ty::Ty,
    ) -> InferResult<Ty> {
        // Convert `ptr` to `&mut`
        let src = if let TyKind::Ptr(PtrKind::Mut(re), path) = src.kind() {
            env.ptr_to_ref(
                &mut infcx.at(span),
                ConstrReason::Other,
                *re,
                path,
                PtrToRefBound::Identity,
            )?
        } else {
            src.clone()
        };

        if let ty::TyKind::Ref(_, deref_ty, _) = dst.kind()
            && let ty::TyKind::Dynamic(..) = deref_ty.kind()
        {
            return Ok(self.refine_default(dst)?);
        }

        // `&mut [T; n] -> &mut [T]` or `&[T; n] -> &[T]`
        if let TyKind::Indexed(BaseTy::Ref(_, deref_ty, _), _) = src.kind()
            && let TyKind::Indexed(BaseTy::Array(arr_ty, arr_len), _) = deref_ty.kind()
            && let ty::TyKind::Ref(re, _, mutbl) = dst.kind()
        {
            let idx = Expr::from_const(self.genv.tcx(), arr_len);
            Ok(Ty::mk_ref(*re, Ty::indexed(BaseTy::Slice(arr_ty.clone()), idx), *mutbl))

        // `Box<[T; n]> -> Box<[T]>`
        } else if let TyKind::Indexed(BaseTy::Adt(adt_def, args), _) = src.kind()
            && adt_def.is_box()
            && let (deref_ty, alloc_ty) = args.box_args()
            && let TyKind::Indexed(BaseTy::Array(arr_ty, arr_len), _) = deref_ty.kind()
        {
            let idx = Expr::from_const(self.genv.tcx(), arr_len);
            Ok(Ty::mk_box(
                self.genv,
                Ty::indexed(BaseTy::Slice(arr_ty.clone()), idx),
                alloc_ty.clone(),
            )?)
        } else {
            Err(query_bug!("unsupported unsize cast from `{src:?}` to `{dst:?}`"))?
        }
    }

    fn check_operands(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        span: Span,
        operands: &[Operand],
    ) -> InferResult<Vec<Ty>> {
        operands
            .iter()
            .map(|op| self.check_operand(infcx, env, span, op))
            .try_collect()
    }

    fn check_operand(
        &mut self,
        infcx: &mut InferCtxt,
        env: &mut TypeEnv,
        span: Span,
        operand: &Operand,
    ) -> InferResult<Ty> {
        let ty = match operand {
            Operand::Copy(p) => env.lookup_place(&mut infcx.at(span), p)?,
            Operand::Move(p) => env.move_place(&mut infcx.at(span), p)?,
            Operand::Constant(c) => self.check_constant(c)?,
        };
        Ok(infcx.hoister(true).hoist(&ty))
    }

    fn check_constant(&mut self, c: &Constant) -> QueryResult<Ty> {
        match c {
            Constant::Int(n, int_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ok(Ty::indexed(BaseTy::Int(*int_ty), idx))
            }
            Constant::Uint(n, uint_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ok(Ty::indexed(BaseTy::Uint(*uint_ty), idx))
            }
            Constant::Bool(b) => {
                let idx = Expr::constant(rty::Constant::from(*b));
                Ok(Ty::indexed(BaseTy::Bool, idx))
            }
            Constant::Float(_, float_ty) => Ok(Ty::float(*float_ty)),
            Constant::Unit => Ok(Ty::unit()),
            Constant::Str(s) => {
                let idx = Expr::constant(rty::Constant::from(*s));
                Ok(Ty::mk_ref(ReStatic, Ty::indexed(BaseTy::Str, idx), Mutability::Not))
            }
            Constant::Char(c) => {
                let idx = Expr::constant(rty::Constant::from(*c));
                Ok(Ty::indexed(BaseTy::Char, idx))
            }
            Constant::Param(param_const, ty) => {
                let idx = Expr::const_generic(*param_const);
                let ctor = self.default_refiner.refine_ty_or_base(ty)?.expect_base();
                Ok(ctor.replace_bound_reft(&idx).to_ty())
            }
            Constant::Opaque(ty) => self.refine_default(ty),
            Constant::Unevaluated(ty, def_id) => {
                let ty = self.refine_default(ty)?;
                let info = self.genv.constant_info(def_id)?;
                let res = if let Some(bty) = ty.as_bty_skipping_existentials()
                    && let rty::ConstantInfo::Interpreted(idx, _) = info
                {
                    Ok(Ty::indexed(bty.clone(), idx))
                } else {
                    Ok(ty)
                };
                res
            }
        }
    }

    fn check_ghost_statements_at(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        point: Point,
        span: Span,
    ) -> Result {
        bug::track_span(span, || {
            for stmt in self.ghost_stmts().statements_at(point) {
                self.check_ghost_statement(infcx, env, stmt, span)
                    .with_span(span)?;
            }
            Ok(())
        })
    }

    fn check_ghost_statement(
        &mut self,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        env: &mut TypeEnv,
        stmt: &GhostStatement,
        span: Span,
    ) -> InferResult {
        dbg::statement!("start", stmt, infcx, env, span, &self);
        match stmt {
            GhostStatement::Fold(place) => {
                env.fold(&mut infcx.at(span), place)?;
            }
            GhostStatement::Unfold(place) => {
                env.unfold(&mut infcx.at(span), place)?;
            }
            GhostStatement::Unblock(place) => env.unblock(infcx, place),
            GhostStatement::PtrToRef(place) => {
                env.ptr_to_ref_at_place(&mut infcx.at(span), place)?;
            }
        }
        dbg::statement!("end", stmt, infcx, env, span, &self);
        Ok(())
    }

    #[track_caller]
    fn marker_at_dominator(&self, bb: BasicBlock) -> &Marker {
        marker_at_dominator(self.body, &self.markers, bb)
    }

    fn dominators(&self) -> &'ck Dominators<BasicBlock> {
        self.body.dominators()
    }

    fn ghost_stmts(&self) -> &'ck GhostStatements {
        &self.inherited.ghost_stmts[&self.def_id]
    }

    fn refine_default(&self, ty: &ty::Ty) -> QueryResult<Ty> {
        ty.refine(&self.default_refiner)
    }

    fn refine_with_holes(&self, ty: &ty::Ty) -> QueryResult<Ty> {
        ty.refine(&Refiner::with_holes(self.genv, self.def_id.to_def_id())?)
    }
}

fn instantiate_args_for_fun_call(
    genv: GlobalEnv,
    caller_id: DefId,
    callee_id: DefId,
    args: &ty::GenericArgs,
) -> QueryResult<Vec<rty::GenericArg>> {
    let params_in_clauses = collect_params_in_clauses(genv, callee_id);

    let hole_refiner = Refiner::new_for_item(genv, caller_id, |bty| {
        let sort = bty.sort();
        let bty = bty.shift_in_escaping(1);
        let constr = if !sort.is_unit() {
            rty::SubsetTy::new(bty, Expr::nu(), Expr::hole(rty::HoleKind::Pred))
        } else {
            rty::SubsetTy::trivial(bty, Expr::nu())
        };
        Binder::bind_with_sort(constr, sort)
    })?;
    let default_refiner = Refiner::default_for_item(genv, caller_id)?;

    let callee_generics = genv.generics_of(callee_id)?;
    args.iter()
        .enumerate()
        .map(|(idx, arg)| {
            let param = callee_generics.param_at(idx, genv)?;
            let refiner =
                if params_in_clauses.contains(&idx) { &default_refiner } else { &hole_refiner };
            refiner.refine_generic_arg(&param, arg)
        })
        .collect()
}

fn instantiate_args_for_constructor(
    genv: GlobalEnv,
    caller_id: DefId,
    adt_id: DefId,
    args: &ty::GenericArgs,
) -> QueryResult<Vec<rty::GenericArg>> {
    let params_in_clauses = collect_params_in_clauses(genv, adt_id);

    let adt_generics = genv.generics_of(adt_id)?;
    let hole_refiner = Refiner::with_holes(genv, caller_id)?;
    let default_refiner = Refiner::default_for_item(genv, caller_id)?;
    args.iter()
        .enumerate()
        .map(|(idx, arg)| {
            let param = adt_generics.param_at(idx, genv)?;
            let refiner =
                if params_in_clauses.contains(&idx) { &default_refiner } else { &hole_refiner };
            refiner.refine_generic_arg(&param, arg)
        })
        .collect()
}

fn collect_params_in_clauses(genv: GlobalEnv, def_id: DefId) -> FxHashSet<usize> {
    let tcx = genv.tcx();
    struct Collector {
        params: FxHashSet<usize>,
    }

    impl rustc_middle::ty::TypeVisitor<TyCtxt<'_>> for Collector {
        fn visit_ty(&mut self, t: rustc_middle::ty::Ty) {
            if let rustc_middle::ty::Param(param_ty) = t.kind() {
                self.params.insert(param_ty.index as usize);
            }
            t.super_visit_with(self);
        }
    }
    let mut vis = Collector { params: Default::default() };

    for (clause, _) in all_predicates_of(tcx, def_id) {
        if let Some(trait_pred) = clause.as_trait_clause() {
            let trait_id = trait_pred.def_id();
            if tcx.require_lang_item(LangItem::Sized, None) == trait_id {
                continue;
            }
            if tcx.require_lang_item(LangItem::Copy, None) == trait_id {
                continue;
            }
            if tcx.fn_trait_kind_from_def_id(trait_id).is_some() {
                continue;
            }
            if tcx.get_diagnostic_item(sym::Hash) == Some(trait_id) {
                continue;
            }
            if tcx.get_diagnostic_item(sym::Eq) == Some(trait_id) {
                continue;
            }
        }
        if let Some(proj_pred) = clause.as_projection_clause() {
            let assoc_id = proj_pred.item_def_id();
            if genv.is_fn_once_output(assoc_id) {
                continue;
            }
        }
        if let Some(outlives_pred) = clause.as_type_outlives_clause() {
            // We skip outlives bounds if they are not 'static. A 'static bound means the type
            // implements `Any` which makes it unsound to instantiate the argument with refinements.
            if outlives_pred.skip_binder().1 != tcx.lifetimes.re_static {
                continue;
            }
        }
        clause.visit_with(&mut vis);
    }
    vis.params
}

fn all_predicates_of(
    tcx: TyCtxt<'_>,
    id: DefId,
) -> impl Iterator<Item = &(rustc_middle::ty::Clause<'_>, Span)> {
    let mut next_id = Some(id);
    iter::from_fn(move || {
        next_id.take().map(|id| {
            let preds = tcx.predicates_of(id);
            next_id = preds.parent;
            preds.predicates.iter()
        })
    })
    .flatten()
}

struct SkipConstr;

impl TypeFolder for SkipConstr {
    fn fold_ty(&mut self, ty: &rty::Ty) -> rty::Ty {
        if let rty::TyKind::Constr(_, inner_ty) = ty.kind() {
            inner_ty.fold_with(self)
        } else {
            ty.super_fold_with(self)
        }
    }
}

fn is_indexed_mut_skipping_constr(ty: &Ty) -> bool {
    let ty = SkipConstr.fold_ty(ty);
    if let rty::Ref!(_, inner_ty, Mutability::Mut) = ty.kind()
        && let TyKind::Indexed(..) = inner_ty.kind()
    {
        true
    } else {
        false
    }
}

/// HACK(nilehmann) This let us infer parameters under mutable references for the simple case
/// where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
/// to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
/// mutable references.
fn infer_under_mut_ref_hack(
    rcx: &mut InferCtxt,
    actuals: &[Ty],
    fn_sig: EarlyBinder<&PolyFnSig>,
) -> Vec<Ty> {
    iter::zip(actuals, fn_sig.skip_binder_ref().skip_binder_ref().inputs())
        .map(|(actual, formal)| {
            if let rty::Ref!(.., Mutability::Mut) = actual.kind()
                && is_indexed_mut_skipping_constr(formal)
            {
                rcx.hoister(false).hoist_inside_mut_refs(true).hoist(actual)
            } else {
                actual.clone()
            }
        })
        .collect()
}

impl Mode for ShapeMode {
    const NAME: &str = "shape";

    fn enter_basic_block<'ck, 'genv, 'tcx>(
        ck: &mut Checker<'ck, 'genv, 'tcx, ShapeMode>,
        _infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        bb: BasicBlock,
    ) -> TypeEnv<'ck> {
        ck.inherited.mode.bb_envs[&ck.def_id][&bb].enter(&ck.body.local_decls)
    }

    fn check_goto_join_point<'genv, 'tcx>(
        ck: &mut Checker<'_, 'genv, 'tcx, ShapeMode>,
        _: InferCtxt<'_, 'genv, 'tcx>,
        env: TypeEnv,
        _: Span,
        target: BasicBlock,
    ) -> Result<bool> {
        let bb_envs = &mut ck.inherited.mode.bb_envs;
        let target_bb_env = bb_envs.entry(ck.def_id).or_default().get(&target);
        dbg::shape_goto_enter!(target, env, target_bb_env);

        let modified = match bb_envs.entry(ck.def_id).or_default().entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(env),
            Entry::Vacant(entry) => {
                let scope = marker_at_dominator(ck.body, &ck.markers, target)
                    .scope()
                    .unwrap_or_else(|| tracked_span_bug!());
                entry.insert(env.into_infer(scope));
                true
            }
        };

        dbg::shape_goto_exit!(target, bb_envs[&ck.def_id].get(&target));
        Ok(modified)
    }

    fn clear(ck: &mut Checker<ShapeMode>, root: BasicBlock) {
        ck.visited.remove(root);
        for bb in ck.body.basic_blocks.indices() {
            if bb != root && ck.dominators().dominates(root, bb) {
                ck.inherited
                    .mode
                    .bb_envs
                    .entry(ck.def_id)
                    .or_default()
                    .remove(&bb);
                ck.visited.remove(bb);
            }
        }
    }
}

impl Mode for RefineMode {
    const NAME: &str = "refine";

    fn enter_basic_block<'ck, 'genv, 'tcx>(
        ck: &mut Checker<'ck, 'genv, 'tcx, RefineMode>,
        infcx: &mut InferCtxt<'_, 'genv, 'tcx>,
        bb: BasicBlock,
    ) -> TypeEnv<'ck> {
        ck.inherited.mode.bb_envs[&ck.def_id][&bb].enter(infcx, &ck.body.local_decls)
    }

    fn check_goto_join_point(
        ck: &mut Checker<RefineMode>,
        mut infcx: InferCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool> {
        let bb_env = &ck.inherited.mode.bb_envs[&ck.def_id][&target];
        debug_assert_eq!(
            &ck.marker_at_dominator(target)
                .scope()
                .unwrap_or_else(|| tracked_span_bug!()),
            bb_env.scope()
        );

        dbg::refine_goto!(target, infcx, env, bb_env);

        env.check_goto(&mut infcx.at(terminator_span), bb_env, target)
            .with_span(terminator_span)?;

        Ok(!ck.visited.contains(target))
    }

    fn clear(_ck: &mut Checker<RefineMode>, _bb: BasicBlock) {
        bug!();
    }
}

fn bool_int_cast(b: &Expr, int_ty: IntTy) -> Ty {
    let idx = Expr::ite(b, 1, 0);
    Ty::indexed(BaseTy::Int(int_ty), idx)
}

fn bool_uint_cast(b: &Expr, uint_ty: UintTy) -> Ty {
    let idx = Expr::ite(b, 1, 0);
    Ty::indexed(BaseTy::Uint(uint_ty), idx)
}

fn int_int_cast(idx: &Expr, int_ty1: IntTy, int_ty2: IntTy) -> Ty {
    if int_bit_width(int_ty1) <= int_bit_width(int_ty2) {
        Ty::indexed(BaseTy::Int(int_ty2), idx.clone())
    } else {
        Ty::int(int_ty2)
    }
}

fn uint_int_cast(idx: &Expr, uint_ty: UintTy, int_ty: IntTy) -> Ty {
    if uint_bit_width(uint_ty) < int_bit_width(int_ty) {
        Ty::indexed(BaseTy::Int(int_ty), idx.clone())
    } else {
        Ty::int(int_ty)
    }
}

fn uint_uint_cast(idx: &Expr, uint_ty1: UintTy, uint_ty2: UintTy) -> Ty {
    if uint_bit_width(uint_ty1) <= uint_bit_width(uint_ty2) {
        Ty::indexed(BaseTy::Uint(uint_ty2), idx.clone())
    } else {
        Ty::uint(uint_ty2)
    }
}

fn uint_bit_width(uint_ty: UintTy) -> u64 {
    uint_ty
        .bit_width()
        .unwrap_or(config::pointer_width().bits())
}

fn int_bit_width(int_ty: IntTy) -> u64 {
    int_ty.bit_width().unwrap_or(config::pointer_width().bits())
}

impl ShapeResult {
    fn into_bb_envs(
        self,
        infcx: &mut InferCtxtRoot,
    ) -> FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnv>> {
        self.0
            .into_iter()
            .map(|(def_id, shapes)| {
                let bb_envs = shapes
                    .into_iter()
                    .map(|(bb, shape)| (bb, shape.into_bb_env(infcx)))
                    .collect();
                (def_id, bb_envs)
            })
            .collect()
    }
}

fn marker_at_dominator<'a>(
    body: &Body,
    markers: &'a IndexVec<BasicBlock, Option<Marker>>,
    bb: BasicBlock,
) -> &'a Marker {
    let dominator = body
        .dominators()
        .immediate_dominator(bb)
        .unwrap_or_else(|| tracked_span_bug!());
    markers[dominator]
        .as_ref()
        .unwrap_or_else(|| tracked_span_bug!())
}

pub(crate) mod errors {
    use flux_errors::{E0999, ErrorGuaranteed};
    use flux_infer::infer::InferErr;
    use flux_middle::{def_id_to_string, global_env::GlobalEnv};
    use rustc_errors::Diagnostic;
    use rustc_hir::def_id::{DefId, LocalDefId};
    use rustc_span::Span;

    use crate::fluent_generated as fluent;

    #[derive(Debug)]
    pub struct CheckerError {
        kind: InferErr,
        span: Span,
    }

    impl CheckerError {
        pub fn opaque_struct(def_id: DefId, span: Span) -> Self {
            Self { kind: InferErr::OpaqueStruct(def_id), span }
        }

        pub fn emit(self, genv: GlobalEnv, fn_def_id: LocalDefId) -> ErrorGuaranteed {
            let dcx = genv.sess().dcx().handle();
            match self.kind {
                InferErr::UnsolvedEvar(_) => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::refineck_param_inference_error);
                    diag.code(E0999);
                    diag.emit()
                }
                InferErr::OpaqueStruct(def_id) => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::refineck_opaque_struct_error);
                    let fn_span = genv.tcx().def_span(fn_def_id);
                    diag.span_help(fn_span, fluent::refineck_opaque_struct_help);
                    diag.note(fluent::refineck_opaque_struct_note);
                    diag.arg("struct", def_id_to_string(def_id));
                    diag.code(E0999);
                    diag.emit()
                }
                InferErr::Query(err) => {
                    let level = rustc_errors::Level::Error;
                    err.at(self.span).into_diag(dcx, level).emit()
                }
            }
        }
    }

    pub trait ResultExt<T> {
        fn with_span(self, span: Span) -> Result<T, CheckerError>;
    }

    impl<T, E> ResultExt<T> for Result<T, E>
    where
        E: Into<InferErr>,
    {
        fn with_span(self, span: Span) -> Result<T, CheckerError> {
            self.map_err(|err| CheckerError { kind: err.into(), span })
        }
    }
}
