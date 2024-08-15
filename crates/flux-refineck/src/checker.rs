use std::{cell::RefCell, collections::hash_map::Entry, iter};

use flux_common::{bug, dbg, index::IndexVec, tracked_span_bug};
use flux_config as config;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty::{
        self, fold::TypeFoldable, refining::Refiner, BaseTy, Binder, Bool, Clause,
        CoroutineObligPredicate, EarlyBinder, Ensures, Expr, FnOutput, FnSig, FnTraitPredicate,
        GenericArg, Generics, HoleKind, Int, IntTy, Mutability, PolyFnSig, PtrKind, Ref,
        Region::ReStatic, Ty, TyKind, Uint, UintTy, VariantIdx,
    },
    rustc::{
        self,
        mir::{
            self, AggregateKind, AssertKind, BasicBlock, Body, BorrowKind, CastKind, Constant,
            Location, Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
            RETURN_PLACE, START_BLOCK,
        },
        ty,
    },
};
use itertools::Itertools;
use rustc_data_structures::{graph::dominators::Dominators, unord::UnordMap};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    LangItem,
};
use rustc_index::bit_set::BitSet;
use rustc_infer::infer::{BoundRegionConversionTime, NllRegionVariableOrigin};
use rustc_middle::{
    mir::{SourceInfo, SwitchTargets},
    ty::{TyCtxt, TypeSuperVisitable as _, TypeVisitable as _},
};
use rustc_span::{sym, Span};

use self::errors::{CheckerError, ResultExt};
use crate::{
    constraint_gen::{ConstrReason, InferCtxt},
    fixpoint_encoding::{self, KVarStore},
    ghost_statements::{GhostStatement, GhostStatements, Point},
    primops,
    queue::WorkQueue,
    refine_tree::{RefineCtxt, RefineSubtree, RefineTree, Snapshot},
    type_env::{BasicBlockEnv, BasicBlockEnvShape, TypeEnv},
};

type Result<T = ()> = std::result::Result<T, CheckerError>;

#[derive(Clone, Copy, Debug)]
pub struct CheckerConfig {
    pub check_overflow: bool,
    pub scrape_quals: bool,
}

pub(crate) struct Checker<'ck, 'genv, 'tcx, M> {
    genv: GlobalEnv<'genv, 'tcx>,
    /// [`LocalDefId`] of the function-like item being checked.
    def_id: LocalDefId,
    /// [`Generics`] of the function being checked.
    generics: Generics,
    inherited: Inherited<'ck, M>,
    body: &'ck Body<'tcx>,
    /// The type used for the `resume` argument if we are checking a generator.
    resume_ty: Option<Ty>,
    output: Binder<FnOutput>,
    /// A snapshot of the refinement context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    visited: BitSet<BasicBlock>,
    queue: WorkQueue<'ck>,
}

/// Fields shared by the top-level function and its nested closure/generators
struct Inherited<'ck, M> {
    /// [`Expr`]s used to instantiate the early bound refinement parameters of the top-level function
    /// signature
    refine_params: List<Expr>,
    ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
    mode: &'ck mut M,
    config: CheckerConfig,
}

impl<'ck, M: Mode> Inherited<'ck, M> {
    fn new(
        genv: GlobalEnv,
        rcx: &mut RefineCtxt,
        def_id: LocalDefId,
        mode: &'ck mut M,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
        config: CheckerConfig,
    ) -> Result<Self> {
        let span = genv.tcx().def_span(def_id);

        let refine_params = genv
            .refinement_generics_of(def_id)
            .with_span(span)?
            .collect_all_params(genv, |param| rcx.define_vars(&param.sort))
            .with_span(span)?;

        Ok(Self { refine_params, ghost_stmts, mode, config })
    }

    fn reborrow(&mut self) -> Inherited<M> {
        Inherited {
            refine_params: self.refine_params.clone(),
            ghost_stmts: self.ghost_stmts,
            mode: &mut *self.mode,
            config: self.config,
        }
    }
}

pub(crate) trait Mode: Sized {
    #[allow(dead_code)] // used for debugging
    const NAME: &str;

    fn constr_gen<'a, 'genv, 'tcx>(
        ck: &'a Checker<'_, 'genv, 'tcx, Self>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> InferCtxt<'a, 'genv, 'tcx>;

    fn enter_basic_block<'ck>(
        ck: &mut Checker<'ck, '_, '_, Self>,
        rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'ck>;

    fn check_goto_join_point(
        ck: &mut Checker<Self>,
        rcx: RefineCtxt,
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
    kvars: RefCell<KVarStore>,
}

/// The result of running the shape phase.
pub(crate) struct ShapeResult(FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnvShape>>);

/// A `Guard` describes extra "control" information that holds at the start of a successor basic block
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
        def_id: LocalDefId,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
        config: CheckerConfig,
    ) -> Result<ShapeResult> {
        dbg::shape_mode_span!(genv.tcx(), def_id).in_scope(|| {
            let span = genv.tcx().def_span(def_id);
            let mut mode = ShapeMode { bb_envs: FxHashMap::default() };
            let generics = genv.generics_of(def_id).with_span(span)?;
            let const_params = generics.const_params(genv).with_span(span)?;
            let mut refine_tree = RefineTree::new(const_params);
            let mut rcx = refine_tree.refine_ctxt_at_root();
            let inherited = Inherited::new(genv, &mut rcx, def_id, &mut mode, ghost_stmts, config)?;

            let body = genv.mir(def_id).with_span(span)?;
            let poly_sig = instantiate_and_normalize_fn_sig(
                genv,
                &inherited,
                &body,
                genv.fn_sig(def_id).with_span(genv.tcx().def_span(def_id))?,
            )?;
            Checker::run(genv, rcx.as_subtree(), def_id, inherited, poly_sig)?;

            Ok(ShapeResult(mode.bb_envs))
        })
    }
}

impl<'ck, 'genv, 'tcx> Checker<'ck, 'genv, 'tcx, RefineMode> {
    pub(crate) fn run_in_refine_mode(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
        ghost_stmts: &'ck UnordMap<LocalDefId, GhostStatements>,
        bb_env_shapes: ShapeResult,
        config: CheckerConfig,
    ) -> Result<(RefineTree, KVarStore)> {
        let span = genv.tcx().def_span(def_id);
        let fn_sig = genv.fn_sig(def_id).with_span(span)?;

        let mut kvars = fixpoint_encoding::KVarStore::new();
        let generics = genv.generics_of(def_id).with_span(span)?;
        let const_params = generics.const_params(genv).with_span(span)?;
        let mut refine_tree = RefineTree::new(const_params);
        let bb_envs = bb_env_shapes.into_bb_envs(&mut kvars);

        dbg::refine_mode_span!(genv.tcx(), def_id, bb_envs).in_scope(|| {
            let mut mode = RefineMode { bb_envs, kvars: RefCell::new(kvars) };
            let mut rcx = refine_tree.refine_ctxt_at_root();
            let inherited = Inherited::new(genv, &mut rcx, def_id, &mut mode, ghost_stmts, config)?;

            let body = genv.mir(def_id).with_span(span)?;
            let poly_sig = instantiate_and_normalize_fn_sig(genv, &inherited, &body, fn_sig)?;

            Checker::run(genv, rcx.as_subtree(), def_id, inherited, poly_sig)?;

            Ok((refine_tree, mode.kvars.into_inner()))
        })
    }
}

#[allow(clippy::too_many_arguments)]
impl<'ck, 'genv, 'tcx, M: Mode> Checker<'ck, 'genv, 'tcx, M> {
    fn run(
        genv: GlobalEnv<'genv, 'tcx>,
        mut refine_tree: RefineSubtree,
        def_id: LocalDefId,
        inherited: Inherited<'ck, M>,
        poly_sig: PolyFnSig,
    ) -> Result {
        let span = genv.tcx().def_span(def_id);

        let body = genv.mir(def_id).with_span(span)?;
        let generics = genv.generics_of(def_id).with_span(span)?;

        let mut rcx = refine_tree.refine_ctxt_at_root();

        // The regions we assign here are not relevant because we would map them to local regions
        // when assigning to locals. See [`TypeEnv::assign`]. Maybe, we should erase regions instead.
        let fn_sig = poly_sig.replace_bound_vars(
            |_| {
                rty::ReVar(
                    body.infcx
                        .next_nll_region_var(NllRegionVariableOrigin::FreeRegion)
                        .as_var(),
                )
            },
            |sort, _| rcx.define_vars(sort),
        );

        let mut env = init_env(&mut rcx, &body, &fn_sig, inherited.config);

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
            generics,
            inherited,
            body: &body,
            resume_ty,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            output: fn_sig.output().clone(),
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            queue: WorkQueue::empty(body.basic_blocks.len(), body.dominators()),
        };

        ck.check_ghost_statements_at(&mut rcx, &mut env, Point::FunEntry, body.span())?;
        ck.check_goto(rcx, env, body.span(), START_BLOCK)?;
        while let Some(bb) = ck.queue.pop() {
            if ck.visited.contains(bb) {
                let snapshot = ck.snapshot_at_dominator(bb);
                refine_tree.clear_children(snapshot);
                M::clear(&mut ck, bb);
            }

            let snapshot = ck.snapshot_at_dominator(bb);
            let mut rcx = refine_tree.refine_ctxt_at(snapshot).unwrap();
            let mut env = M::enter_basic_block(&mut ck, &mut rcx, bb);
            env.unpack(&mut rcx, ck.config().check_overflow);
            ck.check_basic_block(rcx, env, bb)?;
        }

        Ok(())
    }

    fn check_basic_block(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result {
        dbg::basic_block_start!(bb, rcx, env);

        self.visited.insert(bb);
        let data = &self.body.basic_blocks[bb];
        let mut last_stmt_span = None;
        let mut location = Location { block: bb, statement_index: 0 };
        for stmt in &data.statements {
            let span = stmt.source_info.span;
            self.check_ghost_statements_at(
                &mut rcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;
            bug::track_span(span, || {
                dbg::statement!("start", stmt, rcx, env);
                self.check_statement(&mut rcx, &mut env, stmt)?;
                dbg::statement!("end", stmt, rcx, env);
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
                &mut rcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;
            bug::track_span(span, || {
                dbg::terminator!("start", terminator, rcx, env);
                let successors =
                    self.check_terminator(&mut rcx, &mut env, terminator, last_stmt_span)?;
                dbg::terminator!("end", terminator, rcx, env);

                self.snapshots[bb] = Some(rcx.snapshot());
                let term_span = last_stmt_span.unwrap_or(span);
                self.check_successors(rcx, env, bb, term_span, successors)
            })?;
        }
        Ok(())
    }

    fn check_assign_ty(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        place: &Place,
        ty: Ty,
        source_info: SourceInfo,
    ) -> Result {
        let ty = rcx
            .unpacker()
            .assume_invariants(self.check_overflow())
            .unpack(&ty);
        let infcx = &mut self.infcx(rcx, source_info.span);
        env.assign(rcx, infcx, place, ty).with_src_info(source_info)
    }

    fn check_statement(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt: &Statement,
    ) -> Result {
        let stmt_span = stmt.source_info.span;
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rcx, env, stmt_span, rvalue)?;
                self.check_assign_ty(rcx, env, place, ty, stmt.source_info)?;
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
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        terminator: &Terminator<'tcx>,
        last_stmt_span: Option<Span>,
    ) -> Result<Vec<(BasicBlock, Guard)>> {
        let source_info = terminator.source_info;
        let terminator_span = source_info.span;
        match &terminator.kind {
            TerminatorKind::Return => {
                self.check_ret(rcx, env, last_stmt_span.unwrap_or(terminator_span))?;
                Ok(vec![])
            }
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::CoroutineDrop => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::Yield { resume, resume_arg, .. } => {
                if let Some(resume_ty) = self.resume_ty.clone() {
                    self.check_assign_ty(rcx, env, resume_arg, resume_ty, source_info)?;
                } else {
                    bug!("yield in non-generator function");
                }
                Ok(vec![(*resume, Guard::None)])
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.check_operand(rcx, env, terminator_span, discr)?;
                if discr_ty.is_integral() || discr_ty.is_bool() {
                    Ok(Self::check_if(&discr_ty, targets))
                } else {
                    Ok(Self::check_match(&discr_ty, targets))
                }
            }
            TerminatorKind::Call { args, destination, target, resolved_call, .. } => {
                let actuals = self.check_operands(rcx, env, terminator_span, args)?;

                let (func_id, call_args) = resolved_call;
                let fn_sig = self
                    .genv
                    .fn_sig(*func_id)
                    .with_src_info(terminator.source_info)?;

                let generic_args = instantiate_args_for_fun_call(
                    self.genv,
                    &self.generics,
                    *func_id,
                    &call_args.lowered,
                )
                .with_src_info(terminator.source_info)?;

                let ret = self.check_call(
                    rcx,
                    env,
                    terminator_span,
                    *func_id,
                    fn_sig,
                    &generic_args,
                    &actuals,
                )?;

                let ret = rcx.unpack(&ret);
                rcx.assume_invariants(&ret, self.check_overflow());
                let mut gen = self.infcx(rcx, terminator_span);
                env.assign(rcx, &mut gen, destination, ret)
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
                    self.check_assert(rcx, env, terminator_span, cond, *expected, msg)?,
                )])
            }
            TerminatorKind::Drop { place, target, .. } => {
                let _ = env.move_place(self.genv, rcx, place);
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::FalseEdge { real_target, .. } => Ok(vec![(*real_target, Guard::None)]),
            TerminatorKind::FalseUnwind { real_target, .. } => {
                Ok(vec![(*real_target, Guard::None)])
            }
            TerminatorKind::UnwindResume => todo!("implement checking of cleanup code"),
        }
    }

    fn check_ret(&mut self, rcx: &mut RefineCtxt, env: &mut TypeEnv, span: Span) -> Result {
        let mut infcx = self.infcx(rcx, span);

        let ret_place_ty = env
            .lookup_place(self.genv, rcx, Place::RETURN)
            .with_span(span)?;

        let output = self
            .output
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));

        infcx
            .at(ConstrReason::Ret)
            .subtyping(rcx, &ret_place_ty, &output.ret)
            .with_span(span)?;

        for constraint in &output.ensures {
            match constraint {
                Ensures::Type(path, ty) => {
                    let actual_ty = env.get(path);
                    infcx
                        .at(ConstrReason::Ret)
                        .subtyping(rcx, &actual_ty, ty)
                        .with_span(span)?;
                }
                Ensures::Pred(e) => {
                    infcx.at(ConstrReason::Ret).check_pred(rcx, e);
                }
            }
        }

        let clauses = infcx.take_obligations();

        let evars_sol = infcx.solve().with_span(span)?;
        rcx.replace_evars(&evars_sol);

        self.check_closure_clauses(rcx, rcx.snapshot(), &clauses)
    }

    #[allow(clippy::too_many_arguments)]
    fn check_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        span: Span,
        callee_def_id: DefId,
        fn_sig: EarlyBinder<PolyFnSig>,
        generic_args: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<Ty> {
        let genv = self.genv;
        let tcx = genv.tcx();

        let actuals = infer_under_mut_ref_hack(rcx, actuals, fn_sig.as_ref());

        let mut infcx = self.infcx(rcx, span);
        let snapshot = rcx.snapshot();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        // Generate fresh inference variables for refinement arguments
        let refine_args = infcx
            .instantiate_refine_args(callee_def_id)
            .with_span(span)?;

        // Instantiate function signature and normalize it
        let fn_sig = fn_sig
            .instantiate(tcx, &generic_args, &refine_args)
            .replace_bound_vars(
                |br| infcx.next_bound_region_var(span, br.kind, BoundRegionConversionTime::FnCall),
                |sort, mode| infcx.fresh_infer_var(sort, mode),
            )
            .normalize_projections(genv, infcx.region_infcx, infcx.def_id, infcx.refparams)
            .with_span(span)?;

        // Check requires predicates
        for requires in fn_sig.requires() {
            infcx.at(ConstrReason::Call).check_pred(rcx, requires);
        }

        // Check arguments
        for (actual, formal) in iter::zip(actuals, fn_sig.inputs()) {
            let (formal, pred) = formal.unconstr();
            infcx.at(ConstrReason::Call).check_pred(rcx, &pred);
            // TODO(pack-closure): Generalize/refactor to reuse for mutable closures
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path1), TyKind::StrgRef(_, path2, ty2)) => {
                    let ty1 = env.get(path1);
                    infcx.unify_exprs(&path1.to_expr(), &path2.to_expr());
                    infcx
                        .at(ConstrReason::Call)
                        .subtyping(rcx, &ty1, ty2)
                        .with_span(span)?;
                }
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env.block_with(genv, path, bound.clone()).with_span(span)?;
                    infcx
                        .at(ConstrReason::Call)
                        .subtyping(rcx, &ty, bound)
                        .with_span(span)?;
                }
                _ => {
                    infcx
                        .at(ConstrReason::Call)
                        .subtyping(rcx, &actual, &formal)
                        .with_span(span)?
                }
            }
        }

        let clauses = genv
            .predicates_of(callee_def_id)
            .with_span(span)?
            .predicates()
            .instantiate(tcx, &generic_args, &refine_args);

        infcx
            .at(ConstrReason::Call)
            .check_non_closure_clauses(rcx, &clauses)
            .with_span(span)?;

        // Replace evars
        let evars_sol = infcx.solve().with_span(span)?;
        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);

        let output = fn_sig
            .output()
            .replace_evars(&evars_sol)
            .replace_bound_refts_with(|sort, _, _| rcx.define_vars(sort));

        for ensures in &output.ensures {
            match ensures {
                Ensures::Type(path, updated_ty) => {
                    let updated_ty = rcx.unpack(updated_ty);
                    rcx.assume_invariants(&updated_ty, self.check_overflow());
                    env.update_path(path, updated_ty);
                }
                Ensures::Pred(e) => rcx.assume_pred(e),
            }
        }
        self.check_closure_clauses(rcx, snapshot, &clauses)?;

        Ok(output.ret)
    }

    fn check_oblig_generator_pred(
        &mut self,
        rcx: &mut RefineCtxt,
        snapshot: &Snapshot,
        gen_pred: CoroutineObligPredicate,
    ) -> Result {
        // See comment for [`Checker::check_oblig_fn_trait_pred`]
        let poly_sig = instantiate_and_normalize_fn_sig(
            self.genv,
            &self.inherited,
            self.body,
            EarlyBinder(gen_pred.to_poly_fn_sig()),
        )?;
        Checker::run(
            self.genv,
            rcx.subtree_at(snapshot).unwrap(),
            gen_pred.def_id.expect_local(),
            self.inherited.reborrow(),
            poly_sig,
        )
    }

    fn check_oblig_fn_trait_pred(
        &mut self,
        rcx: &mut RefineCtxt,
        snapshot: &Snapshot,
        fn_trait_pred: FnTraitPredicate,
    ) -> Result {
        if let Some(BaseTy::Closure(def_id, tys)) =
            fn_trait_pred.self_ty.as_bty_skipping_existentials()
        {
            // The closure signature may contain region variables generated in the `InferCtxt` of the
            // current function so we normalize it before passing it to `Checker::run`. After
            // normalization, the signature could still contain region variables wich haven't been
            // declared in the closure's `InferCtxt`, but this is fine because we would map them to
            // local regions when assigning to locals. See [`TypeEnv::assign`]
            //
            // After writing this, I realize it may be better to erase regions before normalization.
            // We should revisit this at some point.
            let poly_sig = instantiate_and_normalize_fn_sig(
                self.genv,
                &self.inherited,
                self.body,
                EarlyBinder(fn_trait_pred.to_poly_fn_sig(*def_id, tys.clone())),
            )?;

            Checker::run(
                self.genv,
                rcx.subtree_at(snapshot).unwrap(),
                def_id.expect_local(),
                self.inherited.reborrow(),
                poly_sig,
            )?;
        } else {
            panic!("check_oblig_fn_trait_pred: unexpected self_ty {:?}", fn_trait_pred.self_ty);
        }
        Ok(())
    }

    fn check_closure_clauses(
        &mut self,
        rcx: &mut RefineCtxt,
        snapshot: Snapshot,
        clauses: &[Clause],
    ) -> Result {
        for clause in clauses {
            match clause.kind() {
                rty::ClauseKind::FnTrait(fn_trait_pred) => {
                    self.check_oblig_fn_trait_pred(rcx, &snapshot, fn_trait_pred)?;
                }
                rty::ClauseKind::CoroutineOblig(gen_pred) => {
                    self.check_oblig_generator_pred(rcx, &snapshot, gen_pred)?;
                }
                rty::ClauseKind::Projection(_)
                | rty::ClauseKind::Trait(_)
                | rty::ClauseKind::TypeOutlives(_)
                | rty::ClauseKind::ConstArgHasType(_, _) => {}
            }
        }
        Ok(())
    }

    fn check_assert(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        terminator_span: Span,
        cond: &Operand,
        expected: bool,
        msg: &AssertKind,
    ) -> Result<Guard> {
        let ty = self.check_operand(rcx, env, terminator_span, cond)?;
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
        self.infcx(rcx, terminator_span)
            .at(ConstrReason::Assert(msg))
            .check_pred(rcx, &pred);
        Ok(Guard::Pred(pred))
    }

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
                TyKind::Indexed(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), idx) => {
                    Expr::eq(idx.clone(), Expr::from_bits(bty, bits))
                }
                _ => tracked_span_bug!("unexpected discr_ty {:?}", discr_ty),
            }
        };

        let mut successors = vec![];

        for (bits, bb) in targets.iter() {
            successors.push((bb, Guard::Pred(mk(bits))));
        }
        let otherwise = Expr::and_iter(targets.iter().map(|(bits, _)| mk(bits).not()));
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
            let (_, variant_idx) = remaining.into_iter().next().unwrap();
            successors.push((targets.otherwise(), Guard::Match(place.clone(), variant_idx)));
        } else {
            successors.push((targets.otherwise(), Guard::None));
        }

        successors
    }

    fn check_successors(
        &mut self,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        from: BasicBlock,
        terminator_span: Span,
        successors: Vec<(BasicBlock, Guard)>,
    ) -> Result {
        for (target, guard) in successors {
            let mut rcx = rcx.branch();
            let mut env = env.clone();
            match guard {
                Guard::None => {}
                Guard::Pred(expr) => {
                    rcx.assume_pred(&expr);
                }
                Guard::Match(place, variant_idx) => {
                    env.downcast(self.genv, &mut rcx, &place, variant_idx, self.config())
                        .with_span(terminator_span)?;
                }
            }
            self.check_ghost_statements_at(
                &mut rcx,
                &mut env,
                Point::Edge(from, target),
                terminator_span,
            )?;
            self.check_goto(rcx, env, terminator_span, target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        span: Span,
        target: BasicBlock,
    ) -> Result {
        if self.is_exit_block(target) {
            let location = self.body.terminator_loc(target);
            self.check_ghost_statements_at(
                &mut rcx,
                &mut env,
                Point::BeforeLocation(location),
                span,
            )?;
            self.check_ret(&mut rcx, &mut env, span)
        } else if self.body.is_join_point(target) {
            if M::check_goto_join_point(self, rcx, env, span, target)? {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.check_basic_block(rcx, env, target)
        }
    }

    fn check_rvalue(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt_span: Span,
        rvalue: &Rvalue,
    ) -> Result<Ty> {
        let genv = self.genv;
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(rcx, env, stmt_span, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(rcx, env, stmt_span, *bin_op, op1, op2)
            }
            Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                // TODO(nilehmann) should we somehow connect the result of the operation with the bool?
                let ty = self.check_binary_op(rcx, env, stmt_span, *bin_op, op1, op2)?;
                Ok(Ty::tuple(vec![ty, Ty::bool()]))
            }
            Rvalue::Ref(r, BorrowKind::Mut { .. }, place) => {
                env.borrow(self.genv, rcx, *r, Mutability::Mut, place)
                    .with_span(stmt_span)
            }
            Rvalue::Ref(r, BorrowKind::Shared | BorrowKind::Fake(..), place) => {
                env.borrow(self.genv, rcx, *r, Mutability::Not, place)
                    .with_span(stmt_span)
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(rcx, env, stmt_span, *un_op, op),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, args, _), operands) => {
                let actuals = self.check_operands(rcx, env, stmt_span, operands)?;
                let sig = genv
                    .variant_sig(*def_id, *variant_idx)
                    .with_span(stmt_span)?
                    .ok_or_else(|| CheckerError::opaque_struct(*def_id, stmt_span))?
                    .to_poly_fn_sig();
                let args = instantiate_args_for_constructor(genv, &self.generics, *def_id, args)
                    .with_span(stmt_span)?;
                self.check_call(rcx, env, stmt_span, *def_id, sig, &args, &actuals)
            }
            Rvalue::Aggregate(AggregateKind::Array(arr_ty), operands) => {
                let args = self.check_operands(rcx, env, stmt_span, operands)?;
                let arr_ty = self
                    .genv
                    .refine_with_holes(&self.generics, arr_ty)
                    .with_span(stmt_span)?;
                self.check_mk_array(rcx, env, stmt_span, &args, arr_ty)
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                let tys = self.check_operands(rcx, env, stmt_span, args)?;
                Ok(Ty::tuple(tys))
            }
            Rvalue::Aggregate(AggregateKind::Closure(did, _), operands) => {
                let upvar_tys = self.check_operands(rcx, env, stmt_span, operands)?;
                let res = Ty::closure(*did, upvar_tys);
                Ok(res)
            }
            Rvalue::Aggregate(AggregateKind::Coroutine(did, args), ops) => {
                let args = args.as_coroutine();
                let resume_ty = self
                    .genv
                    .refine_default(&self.generics, args.resume_ty())
                    .with_span(stmt_span)?;
                let upvar_tys = self.check_operands(rcx, env, stmt_span, ops)?;
                Ok(Ty::coroutine(*did, resume_ty, upvar_tys.into()))
            }
            Rvalue::Discriminant(place) => {
                let ty = env
                    .lookup_place(self.genv, rcx, place)
                    .with_span(stmt_span)?;
                let (adt_def, ..) = ty.expect_adt();
                Ok(Ty::discr(adt_def.clone(), place.clone()))
            }
            Rvalue::Len(place) => self.check_len(rcx, env, stmt_span, place),
            Rvalue::Cast(kind, op, to) => {
                let from = self.check_operand(rcx, env, stmt_span, op)?;
                self.check_cast(*kind, &from, to)
            }
            Rvalue::Repeat(operand, c) => {
                let ty = self.check_operand(rcx, env, stmt_span, operand)?;
                Ok(Ty::array(ty, c.clone()))
            }
        }
    }

    fn check_len(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        place: &Place,
    ) -> Result<Ty> {
        let ty = env
            .lookup_place(self.genv, rcx, place)
            .with_span(source_span)?;

        let idx = match ty.kind() {
            TyKind::Indexed(BaseTy::Array(_, len), _) => Expr::from_const(self.genv.tcx(), len),
            TyKind::Indexed(BaseTy::Slice(_), idx) => idx.clone(),
            _ => tracked_span_bug!("expected array or slice type"),
        };

        Ok(Ty::indexed(BaseTy::Uint(UintTy::Usize), idx))
    }

    fn check_binary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        bin_op: mir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Result<Ty> {
        let check_overflow = self.check_overflow();
        let ty1 = self.check_operand(rcx, env, source_span, op1)?;
        let ty2 = self.check_operand(rcx, env, source_span, op2)?;

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                let rule = primops::match_bin_op(bin_op, bty1, idx1, bty2, idx2, check_overflow);
                if let Some(pre) = rule.precondition {
                    self.infcx(rcx, source_span)
                        .at(pre.reason)
                        .check_pred(rcx, pre.pred);
                }

                Ok(rule.output_type)
            }
            _ => tracked_span_bug!("incompatible types: `{ty1:?}` `{ty2:?}`"),
        }
    }

    fn check_unary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        un_op: mir::UnOp,
        op: &Operand,
    ) -> Result<Ty> {
        let ty = self.check_operand(rcx, env, source_span, op)?;
        match ty.kind() {
            TyKind::Indexed(bty, idx) => {
                let rule = primops::match_un_op(un_op, bty, idx, self.check_overflow());
                if let Some(pre) = rule.precondition {
                    self.infcx(rcx, source_span)
                        .at(pre.reason)
                        .check_pred(rcx, pre.pred);
                }
                Ok(rule.output_type)
            }
            _ => tracked_span_bug!("invalid type for unary operator `{un_op:?}` `{ty:?}`"),
        }
    }

    fn check_mk_array(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        span: Span,
        args: &[Ty],
        arr_ty: Ty,
    ) -> Result<Ty> {
        let mut infcx = self.infcx(rcx, span);
        let arr_ty =
            arr_ty.replace_holes(|binders, kind| infcx.fresh_infer_var_for_hole(binders, kind));

        let (arr_ty, pred) = arr_ty.unconstr();
        infcx.at(ConstrReason::Other).check_pred(rcx, &pred);
        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env
                        .block_with(self.genv, path, bound.clone())
                        .with_span(span)?;
                    infcx
                        .at(ConstrReason::Other)
                        .subtyping(rcx, &ty, bound)
                        .with_span(span)?;
                }
                _ => {
                    infcx
                        .at(ConstrReason::Other)
                        .subtyping(rcx, ty, &arr_ty)
                        .with_span(span)?
                }
            }
        }
        rcx.replace_evars(&infcx.solve().with_span(span)?);

        Ok(Ty::array(arr_ty, rty::Const::from_usize(self.genv.tcx(), args.len())))
    }

    fn check_cast(&self, kind: CastKind, from: &Ty, to: &rustc::ty::Ty) -> Result<Ty> {
        use rustc::ty::TyKind as RustTy;
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
                    _ => {
                        tracked_span_bug!("invalid int to int cast")
                    }
                }
            }
            CastKind::Pointer(mir::PointerCast::Unsize) => {
                if let TyKind::Indexed(BaseTy::Ref(_, src_ty, src_mut), _) = from.kind()
                    && let TyKind::Indexed(src_base_ty, _) = src_ty.kind()
                    && let rustc::ty::TyKind::Ref(dst_re, dst_ty, dst_mut) = to.kind()
                {
                    // &mut [T; n] -> &mut [T][n] and &[T; n] -> &[T][n]
                    if let rustc::ty::TyKind::Slice(_) = dst_ty.kind()
                        && let BaseTy::Array(src_arr_ty, src_n) = src_base_ty
                        && src_mut == dst_mut
                    {
                        let idx = Expr::from_const(self.genv.tcx(), src_n);
                        let dst_slice = Ty::indexed(BaseTy::Slice(src_arr_ty.clone()), idx);
                        Ty::mk_ref(*dst_re, dst_slice, *dst_mut)
                    } else
                    // &T  -> & dyn U
                    if let rustc::ty::TyKind::Dynamic(_, _) = dst_ty.kind() {
                        self.genv
                            .refine_default(&self.generics, to)
                            .with_span(self.body.span())?
                    } else {
                        tracked_span_bug!("unsupported Unsize cast: from {from:?} to {to:?}")
                    }
                } else {
                    tracked_span_bug!("unsupported Unsize cast: from {from:?} to {to:?}")
                }
            }
            CastKind::FloatToInt
            | CastKind::IntToFloat
            | CastKind::PtrToPtr
            | CastKind::Pointer(mir::PointerCast::MutToConstPointer)
            | CastKind::PointerWithExposedProvenance => {
                self.genv
                    .refine_default(&self.generics, to)
                    .with_span(self.body.span())?
            }
        };
        Ok(ty)
    }

    fn check_operands(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        operands: &[Operand],
    ) -> Result<Vec<Ty>> {
        operands
            .iter()
            .map(|op| self.check_operand(rcx, env, source_span, op))
            .try_collect()
    }

    fn check_operand(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        operand: &Operand,
    ) -> Result<Ty> {
        let ty = match operand {
            Operand::Copy(p) => env.lookup_place(self.genv, rcx, p).with_span(source_span)?,
            Operand::Move(p) => env.move_place(self.genv, rcx, p).with_span(source_span)?,
            Operand::Constant(c) => self.check_constant(c)?,
        };
        Ok(rcx
            .unpacker()
            .assume_invariants(self.check_overflow())
            .unpack(&ty))
    }

    fn check_constant(&mut self, c: &Constant) -> Result<Ty> {
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
            Constant::Char => Ok(Ty::char()),
            Constant::Param(param_const, ty) => {
                let idx = Expr::const_generic(*param_const, None);
                let ty_ctor = Refiner::default(self.genv, &self.generics)
                    .refine_ty_ctor(ty)
                    .with_span(self.body.span())?;
                Ok(ty_ctor.replace_bound_reft(&idx))
            }
            Constant::Opaque(ty) => {
                self.genv
                    .refine_default(&self.generics, ty)
                    .with_span(self.body.span())
            }
        }
    }

    fn check_ghost_statements_at(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        point: Point,
        span: Span,
    ) -> Result {
        bug::track_span(span, || {
            for stmt in self.ghost_stmts().statements_at(point) {
                self.check_ghost_statement(rcx, env, stmt, span)?;
            }
            Ok(())
        })
    }

    fn check_ghost_statement(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt: &GhostStatement,
        span: Span,
    ) -> Result {
        dbg::statement!("start", stmt, rcx, env);
        match stmt {
            GhostStatement::Fold(place) => {
                let gen = &mut self.infcx(rcx, span);
                env.fold(rcx, gen, place).with_span(span)?;
            }
            GhostStatement::Unfold(place) => {
                env.unfold(self.genv, rcx, place, self.config())
                    .with_span(span)?;
            }
            GhostStatement::Unblock(place) => env.unblock(rcx, place, self.check_overflow()),
            GhostStatement::PtrToBorrow(place) => {
                let gen = &mut self.infcx(rcx, span);
                env.ptr_to_borrow(rcx, gen, place).with_span(span)?;
            }
        }
        dbg::statement!("end", stmt, rcx, env);
        Ok(())
    }

    fn infcx(&self, rcx: &RefineCtxt, span: Span) -> InferCtxt<'_, 'genv, 'tcx> {
        M::constr_gen(self, rcx, span)
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        snapshot_at_dominator(self.body, &self.snapshots, bb)
    }

    fn dominators(&self) -> &'ck Dominators<BasicBlock> {
        self.body.dominators()
    }

    fn ghost_stmts(&self) -> &'ck GhostStatements {
        &self.inherited.ghost_stmts[&self.def_id]
    }

    fn config(&self) -> CheckerConfig {
        self.inherited.config
    }

    fn check_overflow(&self) -> bool {
        self.config().check_overflow
    }
}

fn instantiate_and_normalize_fn_sig<'tcx, M>(
    genv: GlobalEnv<'_, 'tcx>,
    inherited: &Inherited<M>,
    body: &Body<'tcx>,
    fn_sig: EarlyBinder<PolyFnSig>,
) -> Result<PolyFnSig> {
    fn_sig
        .instantiate_identity(&inherited.refine_params)
        .normalize_projections(genv, &body.infcx, body.def_id(), &inherited.refine_params)
        .with_span(body.span())
}

fn init_env<'a>(
    rcx: &mut RefineCtxt,
    body: &'a Body,
    fn_sig: &FnSig,
    config: CheckerConfig,
) -> TypeEnv<'a> {
    let mut env = TypeEnv::new(&body.local_decls);

    for requires in fn_sig.requires() {
        rcx.assume_pred(requires);
    }

    for (local, ty) in body.args_iter().zip(fn_sig.inputs()) {
        let ty = rcx.unpack(ty);
        rcx.assume_invariants(&ty, config.check_overflow);
        env.alloc_with_ty(local, ty);
    }

    for local in body.vars_and_temps_iter() {
        env.alloc(local);
    }

    env.alloc(RETURN_PLACE);
    env
}

fn instantiate_args_for_fun_call(
    genv: GlobalEnv,
    caller_generics: &rty::Generics,
    callee_id: DefId,
    args: &ty::GenericArgs,
) -> QueryResult<Vec<rty::GenericArg>> {
    let params_in_clauses = collect_params_in_clauses(genv, callee_id);

    let callee_generics = genv.generics_of(callee_id)?;
    let hole_refiner = Refiner::new(genv, caller_generics, |bty| {
        let sort = bty.sort();
        let bty = bty.shift_in_escaping(1);
        let constr = if !sort.is_unit() {
            rty::SubsetTy::new(bty, Expr::nu(), Expr::hole(rty::HoleKind::Pred))
        } else {
            rty::SubsetTy::trivial(bty, Expr::nu())
        };
        Binder::with_sort(constr, sort)
    });
    let default_refiner = Refiner::default(genv, caller_generics);

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
    caller_generics: &rty::Generics,
    adt_id: DefId,
    args: &ty::GenericArgs,
) -> QueryResult<Vec<rty::GenericArg>> {
    let params_in_clauses = collect_params_in_clauses(genv, adt_id);

    let adt_generics = genv.generics_of(adt_id)?;
    let hole_refiner = Refiner::with_holes(genv, caller_generics);
    let default_refiner = Refiner::default(genv, caller_generics);
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

    impl<'tcx> rustc_middle::ty::TypeVisitor<TyCtxt<'tcx>> for Collector {
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
            let assoc_id = proj_pred.projection_def_id();
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

/// HACK(nilehmann) This let us infer parameters under mutable references for the simple case
/// where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
/// to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
/// mutable references.
fn infer_under_mut_ref_hack(
    rcx: &mut RefineCtxt,
    actuals: &[Ty],
    fn_sig: EarlyBinder<&PolyFnSig>,
) -> Vec<Ty> {
    iter::zip(
        actuals,
        fn_sig
            .as_ref()
            .skip_binder()
            .as_ref()
            .skip_binder()
            .inputs(),
    )
    .map(|(actual, formal)| {
        if let (Ref!(.., Mutability::Mut), Ref!(_, ty, Mutability::Mut)) =
            (actual.kind(), formal.kind())
            && let TyKind::Indexed(..) = ty.kind()
        {
            rcx.unpacker().unpack_inside_mut_ref(true).unpack(actual)
        } else {
            actual.clone()
        }
    })
    .collect()
}

impl Mode for ShapeMode {
    const NAME: &str = "shape";

    fn constr_gen<'a, 'genv, 'tcx>(
        ck: &'a Checker<'_, 'genv, 'tcx, Self>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt::new(
            ck.genv,
            &ck.body.infcx,
            ck.def_id.into(),
            &ck.inherited.refine_params,
            rcx,
            |_: &[_], _| Expr::hole(HoleKind::Pred),
            span,
        )
    }

    fn enter_basic_block<'a>(
        ck: &mut Checker<'a, '_, '_, ShapeMode>,
        _rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'a> {
        ck.inherited.mode.bb_envs[&ck.def_id][&bb].enter(&ck.body.local_decls)
    }

    fn check_goto_join_point(
        ck: &mut Checker<ShapeMode>,
        _: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool> {
        let bb_envs = &mut ck.inherited.mode.bb_envs;
        let target_bb_env = bb_envs.entry(ck.def_id).or_default().get(&target);
        dbg::shape_goto_enter!(target, env, target_bb_env);

        let modified = match bb_envs.entry(ck.def_id).or_default().entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(env).with_span(terminator_span)?,
            Entry::Vacant(entry) => {
                let scope = snapshot_at_dominator(ck.body, &ck.snapshots, target)
                    .scope()
                    .unwrap();
                entry.insert(env.into_infer(scope).with_span(terminator_span)?);
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

    fn constr_gen<'a, 'genv, 'tcx>(
        ck: &'a Checker<'_, 'genv, 'tcx, Self>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> InferCtxt<'a, 'genv, 'tcx> {
        InferCtxt::new(
            ck.genv,
            &ck.body.infcx,
            ck.def_id.into(),
            &ck.inherited.refine_params,
            rcx,
            {
                let scope = rcx.scope();
                move |sorts: &[_], encoding| {
                    ck.inherited
                        .mode
                        .kvars
                        .borrow_mut()
                        .fresh(sorts, &scope, encoding)
                }
            },
            span,
        )
    }

    fn enter_basic_block<'ck>(
        ck: &mut Checker<'ck, '_, '_, RefineMode>,
        rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'ck> {
        ck.inherited.mode.bb_envs[&ck.def_id][&bb].enter(rcx, &ck.body.local_decls)
    }

    fn check_goto_join_point(
        ck: &mut Checker<RefineMode>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool> {
        let bb_env = &ck.inherited.mode.bb_envs[&ck.def_id][&target];
        debug_assert_eq!(&ck.snapshot_at_dominator(target).scope().unwrap(), bb_env.scope());

        dbg::refine_goto!(target, rcx, env, bb_env);

        let mut infcx = ck.infcx(&rcx, terminator_span);
        env.check_goto(&mut rcx, &mut infcx, bb_env, target)
            .with_span(terminator_span)?;

        Ok(!ck.visited.contains(target))
    }

    fn clear(_ck: &mut Checker<RefineMode>, _bb: BasicBlock) {
        bug!();
    }
}

fn bool_int_cast(b: &Expr, int_ty: IntTy) -> Ty {
    let idx = Expr::ite(b, 1, 0, None);
    Ty::indexed(BaseTy::Int(int_ty), idx)
}

fn bool_uint_cast(b: &Expr, uint_ty: UintTy) -> Ty {
    let idx = Expr::ite(b, 1, 0, None);
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
        kvar_store: &mut KVarStore,
    ) -> FxHashMap<LocalDefId, FxHashMap<BasicBlock, BasicBlockEnv>> {
        self.0
            .into_iter()
            .map(|(def_id, shapes)| {
                let bb_envs = shapes
                    .into_iter()
                    .map(|(bb, shape)| (bb, shape.into_bb_env(kvar_store)))
                    .collect();
                (def_id, bb_envs)
            })
            .collect()
    }
}

fn snapshot_at_dominator<'a>(
    body: &Body,
    snapshots: &'a IndexVec<BasicBlock, Option<Snapshot>>,
    bb: BasicBlock,
) -> &'a Snapshot {
    let dominator = body.dominators().immediate_dominator(bb).unwrap();
    snapshots[dominator].as_ref().unwrap()
}

pub(crate) mod errors {
    use flux_errors::{ErrorGuaranteed, E0999};
    use flux_middle::{pretty, queries::QueryErr, rty::evars::UnsolvedEvar};
    use rustc_errors::Diagnostic;
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir::SourceInfo;
    use rustc_span::Span;

    pub struct CheckerError {
        kind: CheckerErrKind,
        span: Span,
    }

    #[derive(Debug)]
    pub enum CheckerErrKind {
        Inference,
        OpaqueStruct(DefId),
        Query(QueryErr),
    }

    impl CheckerError {
        pub fn opaque_struct(def_id: DefId, span: Span) -> Self {
            Self { kind: CheckerErrKind::OpaqueStruct(def_id), span }
        }
    }

    impl<'a> Diagnostic<'a> for CheckerError {
        fn into_diag(
            self,
            dcx: rustc_errors::DiagCtxtHandle<'a>,
            level: rustc_errors::Level,
        ) -> rustc_errors::Diag<'a, ErrorGuaranteed> {
            use crate::fluent_generated as fluent;

            match self.kind {
                CheckerErrKind::Inference => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::refineck_param_inference_error);
                    diag.code(E0999);
                    diag
                }
                CheckerErrKind::OpaqueStruct(def_id) => {
                    let mut diag =
                        dcx.struct_span_err(self.span, fluent::refineck_opaque_struct_error);
                    diag.arg("struct", pretty::def_id_to_string(def_id));
                    diag.code(E0999);
                    diag
                }
                CheckerErrKind::Query(err) => err.at(self.span).into_diag(dcx, level),
            }
        }
    }

    impl From<QueryErr> for CheckerErrKind {
        fn from(err: QueryErr) -> Self {
            CheckerErrKind::Query(err)
        }
    }

    impl From<UnsolvedEvar> for CheckerErrKind {
        fn from(_: UnsolvedEvar) -> Self {
            CheckerErrKind::Inference
        }
    }

    pub trait ResultExt<T> {
        fn with_span(self, span: Span) -> Result<T, CheckerError>;
        fn with_src_info(self, src_info: SourceInfo) -> Result<T, CheckerError>;
    }

    impl<T, E> ResultExt<T> for Result<T, E>
    where
        E: Into<CheckerErrKind>,
    {
        fn with_span(self, span: Span) -> Result<T, CheckerError> {
            self.map_err(|kind| CheckerError { kind: kind.into(), span })
        }

        fn with_src_info(self, src_info: SourceInfo) -> Result<T, CheckerError> {
            self.map_err(|kind| CheckerError { kind: kind.into(), span: src_info.span })
        }
    }
}
