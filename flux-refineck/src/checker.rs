use std::{collections::hash_map::Entry, fmt, iter};

use flux_common::{
    bug, dbg,
    index::{IndexGen, IndexVec},
    iter::IterExt,
    tracked_span_bug,
};
use flux_config as config;
use flux_middle::{
    global_env::GlobalEnv,
    rty::{
        self, BaseTy, BinOp, Binder, Bool, Constraint, EarlyBinder, Expr, Float, FnOutput, FnSig,
        GenericArg, Generics, Index, Int, IntTy, Mutability, PolyFnSig, Region::ReStatic, Ty,
        TyKind, Uint, UintTy, VariantIdx,
    },
    rustc::{
        self, lowering,
        mir::{
            self, AggregateKind, AssertKind, BasicBlock, Body, BorrowData, BorrowKind, CastKind,
            Constant, Location, Operand, Place, Rvalue, Statement, StatementKind, Terminator,
            TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
        ty::RegionVar,
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir as rustc_mir, ty::RegionVid};
use rustc_span::Span;

use self::errors::{CheckerError, ResultExt};
use crate::{
    constraint_gen::{ConstrGen, ConstrReason, Obligations},
    fixpoint_encoding::{self, KVarStore},
    fold_unfold::{FoldUnfold, FoldUnfolds},
    queue::WorkQueue,
    refine_tree::{RefineCtxt, RefineSubtree, RefineTree, Snapshot},
    sigs,
    type_env::{BasicBlockEnv, BasicBlockEnvShape, TypeEnv},
    ExtraBodyData,
};

#[derive(Clone, Copy, Debug)]
pub struct CheckerConfig {
    pub check_overflow: bool,
    pub scrape_quals: bool,
}

pub(crate) struct Checker<'ck, 'tcx, M> {
    genv: &'ck GlobalEnv<'ck, 'tcx>,
    rvid_gen: IndexGen<RegionVid>,
    config: CheckerConfig,
    /// [`DefId`] of the function being checked, either a closure or a regular function.
    def_id: DefId,
    /// [`Generics`] of the function being checked.
    generics: Generics,
    body: &'ck Body<'tcx>,
    extra_data: &'ck FxHashMap<DefId, ExtraBodyData>,
    output: Binder<FnOutput>,
    mode: &'ck mut M,
    /// A snapshot of the refinement context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    visited: BitSet<BasicBlock>,
    queue: WorkQueue<'ck>,
}

pub(crate) trait Mode: Sized {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rvid_gen: &'a IndexGen<RegionVid>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx>;

    fn enter_basic_block<'ck>(
        ck: &mut Checker<'ck, '_, Self>,
        rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'ck>;

    fn check_goto_join_point(
        ck: &mut Checker<Self>,
        rcx: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool, CheckerError>;

    fn clear(ck: &mut Checker<Self>, bb: BasicBlock);
}

pub(crate) struct ShapeMode {
    bb_envs: FxHashMap<DefId, FxHashMap<BasicBlock, BasicBlockEnvShape>>,
}

pub(crate) struct RefineMode {
    bb_envs: FxHashMap<DefId, FxHashMap<BasicBlock, BasicBlockEnv>>,
    kvars: KVarStore,
}

/// The result of running the shape phase.
pub(crate) struct ShapeResult(FxHashMap<DefId, FxHashMap<BasicBlock, BasicBlockEnvShape>>);

/// A `Guard` describes extra "control" information that holds at the start of a successor basic block
enum Guard {
    /// No extra information holds, e.g., for a plain goto.
    None,
    /// A predicate that can be assumed, e.g., in the branches of an if-then-else.
    Pred(Expr),
    /// The corresponding place was found to be of a particular variant.
    Match(Place, VariantIdx),
}

impl<'a, 'tcx> Checker<'a, 'tcx, ShapeMode> {
    pub(crate) fn run_in_shape_mode(
        genv: &GlobalEnv<'a, 'tcx>,
        def_id: DefId,
        extra_data: &'a FxHashMap<DefId, ExtraBodyData>,
        config: CheckerConfig,
    ) -> Result<ShapeResult, CheckerError> {
        dbg::shape_mode_span!(genv.tcx, def_id).in_scope(|| {
            let mut mode = ShapeMode { bb_envs: FxHashMap::default() };

            let fn_sig = genv
                .fn_sig(def_id)
                .with_span(genv.tcx.def_span(def_id))?
                .subst_identity();

            Checker::run(
                genv,
                RefineTree::new().as_subtree(),
                def_id,
                extra_data,
                &mut mode,
                fn_sig,
                config,
            )?;

            Ok(ShapeResult(mode.bb_envs))
        })
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, RefineMode> {
    pub(crate) fn run_in_refine_mode(
        genv: &GlobalEnv<'a, 'tcx>,
        def_id: DefId,
        extra_data: &'a FxHashMap<DefId, ExtraBodyData>,
        bb_env_shapes: ShapeResult,
        config: CheckerConfig,
    ) -> Result<(RefineTree, KVarStore), CheckerError> {
        let fn_sig = genv
            .fn_sig(def_id)
            .with_span(genv.tcx.def_span(def_id))?
            .subst_identity();

        let mut kvars = fixpoint_encoding::KVarStore::new();
        let mut refine_tree = RefineTree::new();
        let bb_envs = bb_env_shapes.into_bb_envs(&mut kvars);

        dbg::refine_mode_span!(genv.tcx, def_id, bb_envs).in_scope(|| {
            let mut mode = RefineMode { bb_envs, kvars };
            Checker::run(
                genv,
                refine_tree.as_subtree(),
                def_id,
                extra_data,
                &mut mode,
                fn_sig,
                config,
            )?;

            Ok((refine_tree, mode.kvars))
        })
    }
}

impl<'a, 'tcx, M: Mode> Checker<'a, 'tcx, M> {
    fn run(
        genv: &'a GlobalEnv<'a, 'tcx>,
        mut refine_tree: RefineSubtree<'a>,
        def_id: DefId,
        extra_data: &'a FxHashMap<DefId, ExtraBodyData>,
        mode: &'a mut M,
        poly_sig: PolyFnSig,
        config: CheckerConfig,
    ) -> Result<(), CheckerError> {
        let body = genv
            .mir(def_id.expect_local())
            .with_span(genv.tcx.def_span(def_id))?;

        let mut rcx = refine_tree.refine_ctxt_at_root();

        let rvid_gen = IndexGen::new();
        let fn_sig = poly_sig.replace_bound_vars(
            |_| rty::ReVar(RegionVar { rvid: rvid_gen.fresh(), is_nll: false }),
            |sort, _| rcx.define_vars(sort),
        );

        let env = Self::init(&mut rcx, &body, &fn_sig, config);

        let mut ck = Checker {
            def_id,
            genv,
            rvid_gen,
            generics: genv.generics_of(def_id).unwrap(),
            body: &body,
            extra_data,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            output: fn_sig.output().clone(),
            mode,
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            queue: WorkQueue::empty(body.basic_blocks.len(), body.dominators()),
            config,
        };
        ck.check_goto(rcx, env, START_BLOCK, body.span(), START_BLOCK)?;
        while let Some(bb) = ck.queue.pop() {
            if ck.visited.contains(bb) {
                let snapshot = ck.snapshot_at_dominator(bb);
                refine_tree.clear_children(snapshot);
                M::clear(&mut ck, bb);
            }

            let snapshot = ck.snapshot_at_dominator(bb);
            let mut rcx = refine_tree.refine_ctxt_at(snapshot).unwrap();
            let mut env = M::enter_basic_block(&mut ck, &mut rcx, bb);
            env.unpack(&mut rcx);
            ck.check_basic_block(rcx, env, bb)?;
        }

        Ok(())
    }

    fn init<'b>(
        rcx: &mut RefineCtxt,
        body: &'b Body,
        fn_sig: &FnSig,
        config: CheckerConfig,
    ) -> TypeEnv<'b> {
        let mut env = TypeEnv::new(&body.local_decls);

        for constr in fn_sig.requires() {
            match constr {
                rty::Constraint::Type(path, ty) => {
                    let loc = path.to_loc().unwrap();
                    let ty = rcx.unpack(ty);
                    env.alloc_universal_loc(loc, ty);
                }
                rty::Constraint::Pred(e) => {
                    rcx.assume_pred(e.clone());
                }
            }
        }

        for (local, ty) in body.args_iter().zip(fn_sig.args()) {
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

    fn check_basic_block(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result<(), CheckerError> {
        dbg::basic_block_start!(bb, rcx, env);

        self.visited.insert(bb);
        let data = &self.body.basic_blocks[bb];
        let mut last_stmt_span = None;
        let mut location = Location { block: bb, statement_index: 0 };
        for stmt in &data.statements {
            let span = stmt.source_info.span;
            bug::track_span(span, || {
                self.apply_extra_effects_at_location(&mut rcx, &mut env, location, span)?;
                dbg::statement!("start", stmt, rcx, env);
                self.check_statement(&mut rcx, &mut env, stmt)
            })?;
            dbg::statement!("end", stmt, rcx, env);
            if !stmt.is_nop() {
                last_stmt_span = Some(span);
            }
            location = location.successor_within_block();
        }

        if let Some(terminator) = &data.terminator {
            let span = terminator.source_info.span;
            bug::track_span(span, || {
                self.apply_extra_effects_at_location(&mut rcx, &mut env, location, span)?;

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

    fn check_statement(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt: &Statement,
    ) -> Result<(), CheckerError> {
        let stmt_span = stmt.source_info.span;
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rcx, env, stmt_span, rvalue)?;
                let ty = rcx.unpack(&ty);
                let gen = &mut self.constr_gen(rcx, stmt_span);
                env.assign(rcx, gen, place, ty)
                    .with_src_info(stmt.source_info)?;
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
                // otherwise optimized away.
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
    ///    you can assume when checking the correspondnig successor.
    fn check_terminator(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        terminator: &Terminator<'tcx>,
        last_stmt_span: Option<Span>,
    ) -> Result<Vec<(BasicBlock, Guard)>, CheckerError> {
        let terminator_span = terminator.source_info.span;
        match &terminator.kind {
            TerminatorKind::Return => {
                let span = last_stmt_span.unwrap_or(terminator_span);
                self.mode
                    .constr_gen(self.genv, &self.rvid_gen, rcx, span)
                    .check_ret(rcx, env, &self.output)
                    .with_span(span)?;
                Ok(vec![])
            }
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.check_operand(rcx, env, terminator_span, discr)?;
                if discr_ty.is_integral() || discr_ty.is_bool() {
                    Ok(Self::check_if(&discr_ty, targets))
                } else {
                    Ok(Self::check_match(&discr_ty, targets))
                }
            }
            TerminatorKind::Call { args, destination, target, resolved_call, .. } => {
                let (func_id, call_substs) = resolved_call;

                let fn_sig = self
                    .genv
                    .fn_sig(*func_id)
                    .with_src_info(terminator.source_info)?;

                let fn_generics = self
                    .genv
                    .generics_of(*func_id)
                    .with_src_info(terminator.source_info)?;

                let substs = call_substs
                    .lowered
                    .iter()
                    .enumerate()
                    .map(|(idx, arg)| {
                        let param = fn_generics.param_at(idx, self.genv)?;
                        self.genv
                            .instantiate_arg_for_fun(&self.generics, &param, arg)
                    })
                    .try_collect_vec()
                    .with_src_info(terminator.source_info)?;

                let ret = self.check_call(
                    rcx,
                    env,
                    terminator_span,
                    Some(*func_id),
                    fn_sig,
                    &substs,
                    args,
                )?;

                let ret = rcx.unpack(&ret);
                rcx.assume_invariants(&ret, self.config.check_overflow);
                let mut gen = self.constr_gen(rcx, terminator_span);
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
            TerminatorKind::Resume => todo!("implement checking of cleanup code"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        terminator_span: Span,
        did: Option<DefId>,
        fn_sig: EarlyBinder<PolyFnSig>,
        substs: &[GenericArg],
        args: &[Operand],
    ) -> Result<Ty, CheckerError> {
        let actuals = self.check_operands(rcx, env, terminator_span, args)?;

        let (output, obligs) = self
            .constr_gen(rcx, terminator_span)
            .check_fn_call(rcx, env, did, fn_sig, substs, &actuals)
            .with_span(terminator_span)?;

        let output = output.replace_bound_exprs_with(|sort| rcx.define_vars(sort));

        for constr in &output.ensures {
            match constr {
                Constraint::Type(path, updated_ty) => {
                    let updated_ty = rcx.unpack(updated_ty);
                    env.update_path(path, updated_ty);
                }
                Constraint::Pred(e) => rcx.assume_pred(e.clone()),
            }
        }

        self.check_obligs(rcx, obligs)?;

        Ok(output.ret)
    }

    fn check_obligs(
        &mut self,
        rcx: &mut RefineCtxt,
        obligs: Obligations,
    ) -> Result<(), CheckerError> {
        for predicate in &obligs.predicates {
            let fn_trait_pred = predicate.kind().map(|kind| {
                let rty::PredicateKind::FnTrait(fn_trait_pred) = kind;
                fn_trait_pred
            });
            if let Some(BaseTy::Closure(def_id, tys)) = fn_trait_pred
                .self_ty()
                .skip_binder()
                .as_bty_skipping_existentials()
            {
                let refine_tree = rcx.subtree_at(&obligs.snapshot).unwrap();
                Checker::run(
                    self.genv,
                    refine_tree,
                    *def_id,
                    self.extra_data,
                    self.mode,
                    fn_trait_pred.to_closure_sig(*def_id, tys.clone()),
                    self.config,
                )?;
            } else {
                bug!("`Fn*` bounds on a non-closure type are not supported. This should be an error an not an ICE.");
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
    ) -> Result<Guard, CheckerError> {
        let ty = self.check_operand(rcx, env, terminator_span, cond)?;
        let pred = if let TyKind::Indexed(BaseTy::Bool, idx) = ty.kind() {
            if expected {
                idx.expr.clone()
            } else {
                idx.expr.not()
            }
        } else {
            tracked_span_bug!("unexpected ty `{ty:?}`")
        };

        let msg = match msg {
            AssertKind::DivisionByZero => "possible division by zero",
            AssertKind::BoundsCheck => "possible out-of-bounds access",
            AssertKind::RemainderByZero => "possible remainder with a divisor of zero",
            AssertKind::Overflow(mir::BinOp::Div) => "possible division with overflow",
            AssertKind::Overflow(mir::BinOp::Rem) => "possible reminder with overflow",
            AssertKind::Overflow(_) => return Ok(Guard::Pred(pred)),
        };
        self.constr_gen(rcx, terminator_span).check_pred(
            rcx,
            pred.clone(),
            ConstrReason::Assert(msg),
        );
        Ok(Guard::Pred(pred))
    }

    fn check_if(discr_ty: &Ty, targets: &rustc_mir::SwitchTargets) -> Vec<(BasicBlock, Guard)> {
        let mk = |bits| {
            match discr_ty.kind() {
                TyKind::Indexed(BaseTy::Bool, idx) => {
                    if bits == 0 {
                        idx.expr.not()
                    } else {
                        idx.expr.clone()
                    }
                }
                TyKind::Indexed(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), idx) => {
                    Expr::binary_op(BinOp::Eq, idx.expr.clone(), Expr::from_bits(bty, bits), None)
                }
                _ => tracked_span_bug!("unexpected discr_ty {:?}", discr_ty),
            }
        };

        let mut successors = vec![];

        for (bits, bb) in targets.iter() {
            successors.push((bb, Guard::Pred(mk(bits))));
        }
        let otherwise = Expr::and(targets.iter().map(|(bits, _)| mk(bits).not()));
        successors.push((targets.otherwise(), Guard::Pred(otherwise)));

        successors
    }

    fn check_match(discr_ty: &Ty, targets: &rustc_mir::SwitchTargets) -> Vec<(BasicBlock, Guard)> {
        let (adt_def, place) = discr_ty.expect_discr();

        let mut successors = vec![];
        let mut remaining = BitSet::new_filled(adt_def.variants().len());
        for (bits, bb) in targets.iter() {
            let i = bits as usize;
            remaining.remove(i);
            successors.push((bb, Guard::Match(place.clone(), VariantIdx::from_usize(i))));
        }

        if remaining.count() == 1 {
            let i = remaining.iter().next().unwrap();
            successors.push((
                targets.otherwise(),
                Guard::Match(place.clone(), VariantIdx::from_usize(i)),
            ));
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
    ) -> Result<(), CheckerError> {
        for (target, guard) in successors {
            let mut rcx = rcx.branch();
            let mut env = env.clone();
            match guard {
                Guard::None => {}
                Guard::Pred(expr) => {
                    rcx.assume_pred(expr);
                }
                Guard::Match(place, variant_idx) => {
                    env.downcast(self.genv, &mut rcx, &place, variant_idx, self.config)
                        .with_span(terminator_span)?;
                }
            }
            self.check_goto(rcx, env, from, terminator_span, target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        from: BasicBlock,
        span: Span,
        target: BasicBlock,
    ) -> Result<(), CheckerError> {
        self.apply_fold_unfolds_at_edge(&mut rcx, &mut env, from, target, span)?;
        if self.is_exit_block(target) {
            let location = self.body.terminator_loc(target);
            self.apply_extra_effects_at_location(&mut rcx, &mut env, location, span)?;
            self.mode
                .constr_gen(self.genv, &self.rvid_gen, &rcx, span)
                .check_ret(&mut rcx, &mut env, &self.output)
                .with_span(span)
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
    ) -> Result<Ty, CheckerError> {
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
            Rvalue::Ref(r, BorrowKind::Shared, place) => {
                env.borrow(self.genv, rcx, *r, Mutability::Not, place)
                    .with_span(stmt_span)
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(rcx, env, stmt_span, *un_op, op),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let sig = genv
                    .variant_sig(*def_id, *variant_idx)
                    .with_span(stmt_span)?
                    .ok_or_else(|| CheckerError::opaque_struct(*def_id, stmt_span))?
                    .to_poly_fn_sig();
                let adt_generics = &genv.generics_of(*def_id).with_span(stmt_span)?;
                let substs = iter::zip(&adt_generics.params, substs)
                    .map(|(param, arg)| {
                        genv.instantiate_arg_for_constructor(&self.generics, param, arg)
                    })
                    .try_collect_vec()
                    .with_span(stmt_span)?;
                self.check_call(rcx, env, stmt_span, None, sig, &substs, args)
            }
            Rvalue::Aggregate(AggregateKind::Array(arr_ty), args) => {
                let args = self.check_operands(rcx, env, stmt_span, args)?;
                let arr_ty = self
                    .genv
                    .refine_with_holes(&self.generics, arr_ty)
                    .with_span(stmt_span)?;
                let mut gen = self.constr_gen(rcx, stmt_span);
                gen.check_mk_array(rcx, env, &args, arr_ty)
                    .with_span(stmt_span)
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                let tys = self.check_operands(rcx, env, stmt_span, args)?;
                Ok(Ty::tuple(tys))
            }
            Rvalue::Aggregate(AggregateKind::Closure(did, _substs), args) => {
                // TODO(pack-closure): handle case where closure "moves" in values for "free variables"
                let tys = self.check_operands(rcx, env, stmt_span, args)?;
                let mut gen = self.constr_gen(rcx, stmt_span);
                let tys = gen.pack_closure_operands(env, &tys).with_span(stmt_span);

                let res = Ty::closure(*did, tys?);
                Ok(res)
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
        }
    }

    fn check_len(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_span: Span,
        place: &Place,
    ) -> Result<Ty, CheckerError> {
        let ty = env
            .lookup_place(self.genv, rcx, place)
            .with_span(source_span)?;

        let idx = match ty.kind() {
            TyKind::Indexed(BaseTy::Array(_, len), _) => {
                Index::from(Expr::constant(rty::Constant::from(len.val)))
            }
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
    ) -> Result<Ty, CheckerError> {
        let ty1 = self.check_operand(rcx, env, source_span, op1)?;
        let ty2 = self.check_operand(rcx, env, source_span, op2)?;

        match (ty1.kind(), ty2.kind()) {
            (Float!(float_ty1), Float!(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                match bin_op {
                    mir::BinOp::Eq
                    | mir::BinOp::Ne
                    | mir::BinOp::Gt
                    | mir::BinOp::Ge
                    | mir::BinOp::Lt
                    | mir::BinOp::Le => Ok(Ty::bool()),
                    mir::BinOp::Add
                    | mir::BinOp::Sub
                    | mir::BinOp::Mul
                    | mir::BinOp::Div
                    | mir::BinOp::BitAnd
                    | mir::BinOp::BitOr
                    | mir::BinOp::Shl
                    | mir::BinOp::Shr
                    | mir::BinOp::Rem => Ok(Ty::float(*float_ty1)),
                }
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                let sig = sigs::get_bin_op_sig(bin_op, bty1, bty2, self.config.check_overflow);
                let (e1, e2) = (idx1.expr.clone(), idx2.expr.clone());
                if let sigs::Pre::Some(reason, constr) = &sig.pre {
                    self.constr_gen(rcx, source_span).check_pred(
                        rcx,
                        constr([e1.clone(), e2.clone()]),
                        *reason,
                    );
                }

                Ok(sig.out.to_ty([e1, e2]))
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
    ) -> Result<Ty, CheckerError> {
        let ty = self.check_operand(rcx, env, source_span, op)?;
        match ty.kind() {
            Float!(float_ty) => Ok(Ty::float(*float_ty)),
            TyKind::Indexed(bty, idx) => {
                let sig = sigs::get_un_op_sig(un_op, bty, self.config.check_overflow);
                let e = idx.expr.clone();
                if let sigs::Pre::Some(reason, constr) = &sig.pre {
                    self.constr_gen(rcx, source_span)
                        .check_pred(rcx, constr([e.clone()]), *reason);
                }
                Ok(sig.out.to_ty([e]))
            }
            _ => tracked_span_bug!("invalid type for unary operator `{un_op:?}` `{ty:?}`"),
        }
    }

    fn check_cast(
        &self,
        kind: CastKind,
        from: &Ty,
        to: &rustc::ty::Ty,
    ) -> Result<Ty, CheckerError> {
        use rustc::ty::TyKind as RustTy;
        let ty = match kind {
            CastKind::IntToInt => {
                match (from.kind(), to.kind()) {
                    (Bool!(idx), RustTy::Int(int_ty)) => bool_int_cast(&idx.expr, *int_ty),
                    (Bool!(idx), RustTy::Uint(uint_ty)) => bool_uint_cast(&idx.expr, *uint_ty),
                    (Int!(int_ty1, idx), RustTy::Int(int_ty2)) => {
                        int_int_cast(&idx.expr, *int_ty1, *int_ty2)
                    }
                    (Uint!(uint_ty1, idx), RustTy::Uint(uint_ty2)) => {
                        uint_uint_cast(&idx.expr, *uint_ty1, *uint_ty2)
                    }
                    (Uint!(uint_ty, idx), RustTy::Int(int_ty)) => {
                        uint_int_cast(&idx.expr, *uint_ty, *int_ty)
                    }
                    (Int!(_, _), RustTy::Uint(uint_ty)) => Ty::uint(*uint_ty),
                    _ => {
                        tracked_span_bug!("invalid int to int cast")
                    }
                }
            }
            CastKind::FloatToInt
            | CastKind::IntToFloat
            | CastKind::Pointer(mir::PointerCast::MutToConstPointer) => {
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
    ) -> Result<Vec<Ty>, CheckerError> {
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
    ) -> Result<Ty, CheckerError> {
        let ty = match operand {
            Operand::Copy(p) => env.lookup_place(self.genv, rcx, p).with_span(source_span)?,
            Operand::Move(p) => env.move_place(self.genv, rcx, p).with_span(source_span)?,
            Operand::Constant(c) => Self::check_constant(c),
        };
        Ok(rcx.unpack(&ty))
    }

    fn check_constant(c: &Constant) -> Ty {
        match c {
            Constant::Int(n, int_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ty::indexed(BaseTy::Int(*int_ty), idx)
            }
            Constant::Uint(n, uint_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ty::indexed(BaseTy::Uint(*uint_ty), idx)
            }
            Constant::Bool(b) => {
                let idx = Expr::constant(rty::Constant::from(*b));
                Ty::indexed(BaseTy::Bool, idx)
            }
            Constant::Float(_, float_ty) => Ty::float(*float_ty),
            Constant::Unit => Ty::unit(),
            Constant::Str => Ty::mk_ref(ReStatic, Ty::str(), Mutability::Not),
            Constant::Char => Ty::char(),
        }
    }

    fn apply_extra_effects_at_location(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        location: Location,
        span: Span,
    ) -> Result<(), CheckerError> {
        for borrow in self.borrows_out_of_scope_at(location) {
            self.apply_unblock(rcx, env, &UnblockStmt::from(borrow));
        }
        for fold_unfold in self.fold_unfolds().fold_unfolds_at_location(location) {
            self.appy_fold_unfold(rcx, env, fold_unfold, span)?;
        }
        Ok(())
    }

    fn apply_fold_unfolds_at_edge(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        from: BasicBlock,
        target: BasicBlock,
        span: Span,
    ) -> Result<(), CheckerError> {
        for fold_unfold in self.fold_unfolds().fold_unfolds_at_goto(from, target) {
            self.appy_fold_unfold(rcx, env, fold_unfold, span)?;
        }
        Ok(())
    }

    fn apply_unblock(&mut self, rcx: &mut RefineCtxt, env: &mut TypeEnv, stmt: &UnblockStmt) {
        dbg::statement!("start", stmt, rcx, env);
        env.unblock(rcx, &stmt.place);
        dbg::statement!("end", stmt, rcx, env);
    }

    fn appy_fold_unfold(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        fold_unfold: &FoldUnfold,
        span: Span,
    ) -> Result<(), CheckerError> {
        dbg::statement!("start", fold_unfold, rcx, env);
        match fold_unfold {
            FoldUnfold::Fold(place) => {
                let gen = &mut self.constr_gen(rcx, span);
                env.fold(rcx, gen, place)
            }
            FoldUnfold::Unfold(place) => env.unfold(self.genv, rcx, place, self.config),
        }
        .with_span(span)?;
        dbg::statement!("end", fold_unfold, rcx, env);
        Ok(())
    }

    fn constr_gen(&mut self, rcx: &RefineCtxt, span: Span) -> ConstrGen<'_, 'tcx> {
        self.mode.constr_gen(self.genv, &self.rvid_gen, rcx, span)
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators().immediate_dominator(bb).unwrap();
        self.snapshots[dominator].as_ref().unwrap()
    }

    fn fold_unfolds(&self) -> &'a FoldUnfolds {
        &self.extra_data().fold_unfolds
    }

    fn dominators(&self) -> &'a Dominators<BasicBlock> {
        self.body.dominators()
    }

    fn borrows_out_of_scope_at(
        &self,
        location: Location,
    ) -> impl Iterator<Item = &'a BorrowData<'tcx>> {
        self.extra_data()
            .borrows_out_of_scope_at_location
            .get(&location)
            .map_or([].as_slice(), Vec::as_slice)
            .iter()
            .map(|idx| self.body.borrow_data(*idx))
    }

    fn extra_data(&self) -> &'a ExtraBodyData {
        &self.extra_data[&self.def_id]
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
    ) -> FxHashMap<DefId, FxHashMap<BasicBlock, BasicBlockEnv>> {
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

impl Mode for ShapeMode {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rvid_gen: &'a IndexGen<RegionVid>,
        _rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx> {
        ConstrGen::new(genv, |_: &[_], _| Expr::hole(), rvid_gen, span)
    }

    fn enter_basic_block<'a>(
        ck: &mut Checker<'a, '_, ShapeMode>,
        _rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'a> {
        ck.mode.bb_envs[&ck.def_id][&bb].enter(&ck.body.local_decls)
    }

    fn check_goto_join_point(
        ck: &mut Checker<ShapeMode>,
        _: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool, CheckerError> {
        // TODO(nilehmann) we should only ask for the scope in the vacant branch
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();

        let target_bb_env = ck.mode.bb_envs.entry(ck.def_id).or_default().get(&target);
        dbg::shape_goto_enter!(target, env, target_bb_env);

        let modified = match ck.mode.bb_envs.entry(ck.def_id).or_default().entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(env).with_span(terminator_span)?,
            Entry::Vacant(entry) => {
                entry.insert(env.into_infer(scope).with_span(terminator_span)?);
                true
            }
        };

        dbg::shape_goto_exit!(target, ck.mode.bb_envs[&ck.def_id].get(&target));
        Ok(modified)
    }

    fn clear(ck: &mut Checker<ShapeMode>, root: BasicBlock) {
        ck.visited.remove(root);
        for bb in ck.body.basic_blocks.indices() {
            if bb != root && ck.dominators().dominates(root, bb) {
                ck.mode.bb_envs.entry(ck.def_id).or_default().remove(&bb);
                ck.visited.remove(bb);
            }
        }
    }
}

impl Mode for RefineMode {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rvid_gen: &'a IndexGen<RegionVid>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx> {
        let scope = rcx.scope();
        ConstrGen::new(
            genv,
            move |sorts: &[_], encoding| self.kvars.fresh_bound(sorts, scope.iter(), encoding),
            rvid_gen,
            span,
        )
    }

    fn enter_basic_block<'a>(
        ck: &mut Checker<'a, '_, RefineMode>,
        rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv<'a> {
        ck.mode.bb_envs[&ck.def_id][&bb].enter(rcx, &ck.body.local_decls)
    }

    fn check_goto_join_point(
        ck: &mut Checker<RefineMode>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool, CheckerError> {
        let bb_env = &ck.mode.bb_envs[&ck.def_id][&target];
        debug_assert_eq!(&ck.snapshot_at_dominator(target).scope().unwrap(), bb_env.scope());

        dbg::refine_goto!(target, rcx, env, bb_env);

        let gen = &mut ConstrGen::new(
            ck.genv,
            |sorts: &[_], encoding| {
                ck.mode
                    .kvars
                    .fresh_bound(sorts, bb_env.scope().iter(), encoding)
            },
            &ck.rvid_gen,
            terminator_span,
        );
        env.check_goto(&mut rcx, gen, bb_env, target)
            .with_span(terminator_span)?;

        Ok(!ck.visited.contains(target))
    }

    fn clear(_ck: &mut Checker<RefineMode>, _bb: BasicBlock) {
        bug!();
    }
}

pub(crate) mod errors {
    use flux_errors::ErrorGuaranteed;
    use flux_middle::{pretty, queries::QueryErr, rty::evars::UnsolvedEvar};
    use rustc_errors::IntoDiagnostic;
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir::SourceInfo;
    use rustc_span::Span;

    pub struct CheckerError {
        kind: CheckerErrKind,
        span: Span,
    }

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

    impl<'a> IntoDiagnostic<'a> for CheckerError {
        fn into_diagnostic(
            self,
            handler: &'a rustc_errors::Handler,
        ) -> rustc_errors::DiagnosticBuilder<'a, ErrorGuaranteed> {
            use crate::fluent_generated as fluent;
            let mut builder = match self.kind {
                CheckerErrKind::Inference => {
                    handler.struct_err_with_code(
                        fluent::refineck_param_inference_error,
                        flux_errors::diagnostic_id(),
                    )
                }
                CheckerErrKind::OpaqueStruct(def_id) => {
                    let mut builder = handler.struct_err_with_code(
                        fluent::refineck_opaque_struct_error,
                        flux_errors::diagnostic_id(),
                    );
                    builder.set_arg("struct", pretty::def_id_to_string(def_id));
                    builder
                }
                CheckerErrKind::Query(err) => err.into_diagnostic(handler),
            };
            builder.set_span(self.span);

            builder
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

    pub trait ResultExt {
        type Ok;
        fn with_span(self, span: Span) -> Result<Self::Ok, CheckerError>;
        fn with_src_info(self, src_info: SourceInfo) -> Result<Self::Ok, CheckerError>;
    }

    impl<T, E> ResultExt for Result<T, E>
    where
        E: Into<CheckerErrKind>,
    {
        type Ok = T;

        fn with_span(self, span: Span) -> Result<T, CheckerError> {
            self.map_err(|kind| CheckerError { kind: kind.into(), span })
        }

        fn with_src_info(self, src_info: SourceInfo) -> Result<T, CheckerError> {
            self.map_err(|kind| CheckerError { kind: kind.into(), span: src_info.span })
        }
    }
}

struct UnblockStmt {
    place: Place,
}

impl From<&BorrowData<'_>> for UnblockStmt {
    fn from(borrow: &BorrowData) -> Self {
        UnblockStmt { place: lowering::lower_place(&borrow.borrowed_place).unwrap() }
    }
}

impl fmt::Debug for UnblockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unblock({:?})", self.place)
    }
}
