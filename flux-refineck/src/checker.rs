use std::{
    collections::{hash_map::Entry, BinaryHeap},
    iter,
};

use flux_common::{bug, dbg, index::IndexVec, iter::IterExt, span_bug, tracked_span_bug};
use flux_config as config;
use flux_middle::{
    global_env::GlobalEnv,
    rty::{
        self, BaseTy, BinOp, Binder, Bool, Constraint, Expr, Float, FnOutput, FnSig, GenericArg,
        Generics, Index, Int, IntTy, PolySig, RefKind, Sort, Ty, TyKind, Uint, UintTy, VariantIdx,
    },
    rustc::{
        self,
        mir::{
            self, AggregateKind, AssertKind, BasicBlock, Body, CastKind, Constant, Operand, Place,
            Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
            START_BLOCK,
        },
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir as rustc_mir;
use rustc_span::Span;

use self::errors::{CheckerError, ResultExt};
use crate::{
    constraint_gen::{ConstrGen, ConstrReason, Obligations},
    fixpoint_encoding::{self, KVarStore},
    refine_tree::{RefineCtxt, RefineSubtree, RefineTree, Snapshot},
    sigs,
    type_env::{BasicBlockEnv, BasicBlockEnvShape, TypeEnv},
};

pub(crate) struct Checker<'a, 'tcx, M> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    /// [`DefId`] of the function being checked, either a closure or a regular function.
    def_id: DefId,
    /// [`Generics`] of the function being checked.
    generics: Generics,
    body: &'a Body<'tcx>,
    mode: &'a mut M,
    output: Binder<FnOutput>,
    /// A snapshot of the refinement context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: &'a Dominators<BasicBlock>,
    visited: BitSet<BasicBlock>,
    queue: WorkQueue<'a>,
}

pub(crate) trait Mode: Sized {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx>;

    fn enter_basic_block(ck: &mut Checker<Self>, rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv;

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

impl<'a, 'tcx, M> Checker<'a, 'tcx, M> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        def_id: DefId,
        body: &'a Body<'tcx>,
        output: Binder<FnOutput>,
        dominators: &'a Dominators<BasicBlock>,
        mode: &'a mut M,
    ) -> Self {
        let generics = genv.generics_of(def_id).unwrap_or_else(|_| {
            span_bug!(body.span(), "checking function with unsupported signature")
        });
        Checker {
            def_id,
            genv,
            generics,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            output,
            mode,
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            dominators,
            queue: WorkQueue::empty(body.basic_blocks.len(), dominators),
        }
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, ShapeMode> {
    pub(crate) fn run_in_shape_mode(
        genv: &GlobalEnv<'a, 'tcx>,
        def_id: DefId,
    ) -> Result<ShapeResult, CheckerError> {
        dbg::shape_mode_span!(genv.tcx, def_id).in_scope(|| {
            let mut mode = ShapeMode { bb_envs: FxHashMap::default() };

            let fn_sig = genv.fn_sig(def_id).unwrap_or_else(|_| {
                span_bug!(genv.tcx.def_span(def_id), "checking function with unsupported signature")
            });

            Checker::run(genv, RefineTree::new().as_subtree(), def_id, &mut mode, fn_sig)?;

            Ok(ShapeResult(mode.bb_envs))
        })
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, RefineMode> {
    pub(crate) fn run_in_refine_mode(
        genv: &GlobalEnv<'a, 'tcx>,
        def_id: DefId,
        bb_env_shapes: ShapeResult,
    ) -> Result<(RefineTree, KVarStore), CheckerError> {
        let fn_sig = genv.fn_sig(def_id).unwrap_or_else(|_| {
            span_bug!(genv.tcx.def_span(def_id), "checking function with unsupported signature")
        });
        let mut kvars = fixpoint_encoding::KVarStore::new();
        let mut refine_tree = RefineTree::new();
        let bb_envs = bb_env_shapes.into_bb_envs(&mut kvars);

        dbg::refine_mode_span!(genv.tcx, def_id, bb_envs).in_scope(|| {
            let mut mode = RefineMode { bb_envs, kvars };
            Checker::run(genv, refine_tree.as_subtree(), def_id, &mut mode, fn_sig)?;

            Ok((refine_tree, mode.kvars))
        })
    }
}

impl<'a, 'tcx, M: Mode> Checker<'a, 'tcx, M> {
    fn run(
        genv: &'a GlobalEnv<'a, 'tcx>,
        mut refine_tree: RefineSubtree<'a>,
        def_id: DefId,
        mode: &'a mut M,
        fn_sig: PolySig,
    ) -> Result<(), CheckerError> {
        let body = {
            let local_def_id = def_id.as_local().unwrap();
            let mir =
                unsafe { flux_common::mir_storage::retrieve_mir_body(genv.tcx, local_def_id) };
            rustc::lowering::LoweringCtxt::lower_mir_body(genv.tcx, genv.sess, mir).unwrap()
        };

        let mut rcx = refine_tree.refine_ctxt_at_root();

        let fn_sig = fn_sig.replace_bvars_with(|sort, _| rcx.define_vars(sort));

        let env = Self::init(&mut rcx, &body, &fn_sig);

        let dominators = body.dominators();

        let mut ck = Checker::new(genv, def_id, &body, fn_sig.output().clone(), &dominators, mode);

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
            env.unpack(&mut rcx);
            ck.check_basic_block(rcx, env, bb)?;
        }

        Ok(())
    }

    fn init(rcx: &mut RefineCtxt, body: &Body, fn_sig: &FnSig) -> TypeEnv {
        let mut env = TypeEnv::new();

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
            rcx.assume_invariants(&ty);
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
        for stmt in &data.statements {
            dbg::statement!("start", stmt, rcx, env);
            bug::track_span(stmt.source_info.span, || {
                self.check_statement(&mut rcx, &mut env, stmt)
            })?;
            dbg::statement!("end", stmt, rcx, env);
            if !stmt.is_nop() {
                last_stmt_span = Some(stmt.source_info.span);
            }
        }

        if let Some(terminator) = &data.terminator {
            bug::track_span(terminator.source_info.span, || {
                dbg::terminator!("start", terminator, rcx, env);
                let successors =
                    self.check_terminator(&mut rcx, &mut env, terminator, last_stmt_span)?;
                dbg::terminator!("end", terminator, rcx, env);

                self.snapshots[bb] = Some(rcx.snapshot());
                let term_span = last_stmt_span.unwrap_or(terminator.source_info.span);
                self.check_successors(rcx, env, term_span, successors)
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
                // println!("TRACE: check_statement {stmt:?}");
                let ty = self.check_rvalue(rcx, env, stmt_span, rvalue)?;
                let ty = rcx.unpack(&ty);
                let gen = &mut self.constr_gen(rcx, stmt_span);
                env.write_place(rcx, gen, place, ty)
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
                    .constr_gen(self.genv, rcx, span)
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
                rcx.assume_invariants(&ret);
                let mut gen = self.constr_gen(rcx, terminator_span);
                env.write_place(rcx, &mut gen, destination, ret)
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
                let mut gen = self.constr_gen(rcx, terminator_span);
                let _ = env.move_place(rcx, &mut gen, place);
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
        fn_sig: PolySig,
        substs: &[GenericArg],
        args: &[Operand],
    ) -> Result<Ty, CheckerError> {
        let actuals = self.check_operands(rcx, env, terminator_span, args)?;

        let (output, obligs) = self
            .constr_gen(rcx, terminator_span)
            .check_fn_call(rcx, env, did, &fn_sig, substs, &actuals)
            .with_span(terminator_span)?;

        let output = output.replace_bvar_with(|sort| rcx.define_vars(sort));

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
        for predicate in obligs.predicates {
            match predicate {
                rty::Predicate::FnTrait(fn_pred) => {
                    if let Some(BaseTy::Closure(def_id)) =
                        fn_pred.bounded_ty.as_bty_skipping_binders()
                    {
                        let refine_tree = rcx.subtree_at(&obligs.snapshot).unwrap();
                        Checker::run(
                            self.genv,
                            refine_tree,
                            *def_id,
                            self.mode,
                            fn_pred.to_poly_sig(*def_id),
                        )?;
                    } else {
                        todo!("report error")
                    }
                }
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
                    Expr::binary_op(BinOp::Eq, idx.expr.clone(), Expr::from_bits(bty, bits))
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
        let mut remaining = BitSet::new_filled(adt_def.nvariants());
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
                    env.downcast(self.genv, &mut rcx, &place, variant_idx)
                        .with_span(terminator_span)?;
                }
            }
            self.check_goto(rcx, env, terminator_span, target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        source_span: Span,
        target: BasicBlock,
    ) -> Result<(), CheckerError> {
        if self.is_exit_block(target) {
            self.mode
                .constr_gen(self.genv, &rcx, source_span)
                .check_ret(&mut rcx, &mut env, &self.output)
                .with_span(source_span)
        } else if self.body.is_join_point(target) {
            if M::check_goto_join_point(self, rcx, env, source_span, target)? {
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
            Rvalue::MutRef(place) => {
                let gen = &mut self.constr_gen(rcx, stmt_span);
                env.borrow(rcx, gen, RefKind::Mut, place)
                    .with_span(stmt_span)
            }
            Rvalue::ShrRef(place) => {
                let gen = &mut self.constr_gen(rcx, stmt_span);
                env.borrow(rcx, gen, RefKind::Shr, place)
                    .with_span(stmt_span)
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(rcx, env, stmt_span, *un_op, op),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let sig = genv
                    .variant(*def_id, *variant_idx)
                    .with_span(stmt_span)?
                    .ok_or_else(|| CheckerError::opaque_struct(*def_id, stmt_span))?
                    .to_fn_sig();
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
            Rvalue::Aggregate(AggregateKind::Closure(did, substs), args) => {
                if args.is_empty() {
                    // TODO (RJ): handle case where closure "moves" in values for "free variables"
                    // let substs = substs.iter().map(|arg| *arg).collect_vec();
                    Ok(Ty::closure(*did))
                } else {
                    panic!("TODO: check the closure defid = {did:?}, substs = {substs:?}, args = {args:?}")
                }
            }
            Rvalue::Discriminant(place) => {
                let gen = &mut self.constr_gen(rcx, stmt_span);
                let ty = env.lookup_place(rcx, gen, place).with_span(stmt_span)?;
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
        let gen = &mut self.constr_gen(rcx, source_span);
        let ty = env.lookup_place(rcx, gen, place).with_span(source_span)?;

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
                let sig = sigs::get_bin_op_sig(bin_op, bty1, bty2);
                let (e1, e2) = (idx1.expr.clone(), idx2.expr.clone());
                if let sigs::Pre::Some(reason, constr) = &sig.pre {
                    self.constr_gen(rcx, source_span).check_pred(
                        rcx,
                        constr([e1.clone(), e2.clone()]),
                        *reason,
                    );
                }

                match sig.out.clone() {
                    sigs::Output::Indexed(bty, mk) => Ok(Ty::indexed(bty, mk([e1, e2]))),
                    sigs::Output::Exists(bty, mk) => {
                        Ok(Ty::exists_with_constr(bty, mk(Expr::nu(), [e1, e2])))
                    }
                }
            }
            _ => tracked_span_bug!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
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
        let ty = match un_op {
            mir::UnOp::Not => {
                if let Bool!(idx) = ty.kind() {
                    Ty::indexed(BaseTy::Bool, idx.expr.not())
                } else {
                    tracked_span_bug!("incompatible type: `{:?}`", ty)
                }
            }
            mir::UnOp::Neg => {
                match ty.kind() {
                    Int!(int_ty, idx) => Ty::indexed(BaseTy::Int(*int_ty), idx.expr.neg()),
                    Float!(float_ty) => Ty::float(*float_ty),
                    _ => tracked_span_bug!("incompatible type: `{:?}`", ty),
                }
            }
        };
        Ok(ty)
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
            Operand::Copy(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self.constr_gen(rcx, source_span);
                env.lookup_place(rcx, gen, p).with_span(source_span)?
            }
            Operand::Move(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self.constr_gen(rcx, source_span);
                env.move_place(rcx, gen, p).with_span(source_span)?
            }
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
            Constant::Str => Ty::mk_ref(RefKind::Shr, Ty::str()),
            Constant::Char => Ty::char(),
        }
    }

    fn constr_gen(&mut self, rcx: &RefineCtxt, span: Span) -> ConstrGen<'_, 'tcx> {
        self.mode.constr_gen(self.genv, rcx, span)
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
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
        _rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx> {
        ConstrGen::new(genv, |_: &[Sort], _| Expr::hole(), span)
    }

    fn enter_basic_block(
        ck: &mut Checker<ShapeMode>,
        _rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv {
        ck.mode.bb_envs[&ck.def_id][&bb].enter()
    }

    fn check_goto_join_point(
        ck: &mut Checker<ShapeMode>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        terminator_span: Span,
        target: BasicBlock,
    ) -> Result<bool, CheckerError> {
        // TODO(nilehmann) we should only ask for the scope in the vacant branch
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();

        let target_bb_env = ck.mode.bb_envs.entry(ck.def_id).or_default().get(&target);
        dbg::shape_goto_enter!(target, env, target_bb_env);

        let mut gen = ConstrGen::new(ck.genv, |_: &[Sort], _| Expr::hole(), terminator_span);

        let modified = match ck.mode.bb_envs.entry(ck.def_id).or_default().entry(target) {
            Entry::Occupied(mut entry) => {
                entry
                    .get_mut()
                    .join(&mut rcx, &mut gen, env)
                    .with_span(terminator_span)?
            }
            Entry::Vacant(entry) => {
                entry.insert(
                    env.into_infer(&mut rcx, &mut gen, scope)
                        .with_span(terminator_span)?,
                );
                true
            }
        };

        dbg::shape_goto_exit!(target, ck.mode.bb_envs[&ck.def_id].get(&target));
        Ok(modified)
    }

    fn clear(ck: &mut Checker<ShapeMode>, root: BasicBlock) {
        ck.visited.remove(root);
        for bb in ck.body.basic_blocks.indices() {
            if bb != root && ck.dominators.dominates(root, bb) {
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
        rcx: &RefineCtxt,
        span: Span,
    ) -> ConstrGen<'a, 'tcx> {
        let scope = rcx.scope();
        ConstrGen::new(
            genv,
            move |sorts: &[Sort], encoding| self.kvars.fresh_bound(sorts, scope.iter(), encoding),
            span,
        )
    }

    fn enter_basic_block(
        ck: &mut Checker<RefineMode>,
        rcx: &mut RefineCtxt,
        bb: BasicBlock,
    ) -> TypeEnv {
        ck.mode.bb_envs[&ck.def_id][&bb].enter(rcx)
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
            |sorts: &[Sort], encoding| {
                ck.mode
                    .kvars
                    .fresh_bound(sorts, bb_env.scope().iter(), encoding)
            },
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

struct Item<'a> {
    bb: BasicBlock,
    dominators: &'a Dominators<BasicBlock>,
}

struct WorkQueue<'a> {
    heap: BinaryHeap<Item<'a>>,
    set: BitSet<BasicBlock>,
    dominators: &'a Dominators<BasicBlock>,
}

impl<'a> WorkQueue<'a> {
    fn empty(len: usize, dominators: &'a Dominators<BasicBlock>) -> Self {
        Self { heap: BinaryHeap::with_capacity(len), set: BitSet::new_empty(len), dominators }
    }

    fn insert(&mut self, bb: BasicBlock) -> bool {
        if self.set.insert(bb) {
            self.heap.push(Item { bb, dominators: self.dominators });
            true
        } else {
            false
        }
    }

    fn pop(&mut self) -> Option<BasicBlock> {
        if let Some(Item { bb, .. }) = self.heap.pop() {
            self.set.remove(bb);
            Some(bb)
        } else {
            None
        }
    }
}

impl PartialEq for Item<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.bb == other.bb
    }
}

impl PartialOrd for Item<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.dominators.rank_partial_cmp(other.bb, self.bb)
    }
}

impl Eq for Item<'_> {}

impl Ord for Item<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
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
