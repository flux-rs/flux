extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{hash_map::Entry, BinaryHeap};

use flux_common::{
    config::{AssertBehavior, CONFIG},
    index::IndexVec,
};
use flux_middle::{
    global_env::GlobalEnv,
    rty::{
        self, BaseTy, BinOp, Binders, Bool, Const, Constraint, Constraints, Expr, Float, FnSig,
        Int, IntTy, PolySig, RefKind, RefineArgs, Sort, Ty, TyKind, Uint, UintTy, VariantIdx,
    },
    rustc::{
        self,
        mir::{
            self, AggregateKind, AssertKind, BasicBlock, Body, CastKind, Constant, Operand, Place,
            Rvalue, SourceInfo, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
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

use self::errors::CheckerError;
use crate::{
    constraint_gen::{ConstrGen, Tag},
    dbg,
    fixpoint::{KVarEncoding, KVarStore},
    refine_tree::{RefineCtxt, RefineTree, Snapshot, UnpackFlags},
    sigs,
    type_env::{BasicBlockEnv, TypeEnv, TypeEnvInfer},
};

pub struct Checker<'a, 'tcx, P> {
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    genv: &'a GlobalEnv<'a, 'tcx>,
    phase: P,
    ret: Ty,
    ensures: Constraints,
    /// A snapshot of the pure context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: &'a Dominators<BasicBlock>,
    queue: WorkQueue<'a>,
}

pub trait Phase: Sized {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &RefineCtxt,
        tag: Tag,
    ) -> ConstrGen<'a, 'tcx>;

    fn enter_basic_block(&mut self, rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv;

    fn check_goto_join_point(
        ck: &mut Checker<Self>,
        rcx: RefineCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<bool, CheckerError>;

    fn fresh_kvar(&mut self, sorts: &[Sort], encoding: KVarEncoding) -> Binders<Expr>;

    fn clear(&mut self, bb: BasicBlock);
}

pub struct Inference<'a> {
    bb_envs: &'a mut FxHashMap<BasicBlock, TypeEnvInfer>,
}

pub struct Check<'a> {
    bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
    kvars: &'a mut KVarStore,
}

/// A `Guard` describes extra "control" information that holds at the start
/// of the successor basic block
enum Guard {
    /// No extra information holds, e.g., for a plain goto.
    None,
    /// A predicate that can be assumed, e.g., an if-then-else or while-do boolean condition.
    Pred(Expr),
    // The corresponding place was found to be of a particular variant.
    Match(Place, VariantIdx),
}

impl<'a, 'tcx, P> Checker<'a, 'tcx, P> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        body: &'a Body<'tcx>,
        ret: Ty,
        ensures: Constraints,
        dominators: &'a Dominators<BasicBlock>,
        phase: P,
    ) -> Self {
        Checker {
            genv,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            ret,
            ensures,
            phase,
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            dominators,
            queue: WorkQueue::empty(body.basic_blocks.len(), dominators),
        }
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Inference<'_>> {
    pub fn infer(
        genv: &GlobalEnv<'a, 'tcx>,
        body: &Body<'tcx>,
        def_id: DefId,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvInfer>, CheckerError> {
        dbg::infer_span!(genv.tcx, def_id).in_scope(|| {
            let mut refine_tree = RefineTree::new();
            let mut bb_envs = FxHashMap::default();
            Checker::run(
                genv,
                &mut refine_tree,
                body,
                def_id,
                Inference { bb_envs: &mut bb_envs },
            )?;

            Ok(bb_envs)
        })
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Check<'_>> {
    pub fn check(
        genv: &GlobalEnv<'a, 'tcx>,
        body: &Body<'tcx>,
        def_id: DefId,
        kvars: &mut KVarStore,
        bb_envs_infer: FxHashMap<BasicBlock, TypeEnvInfer>,
    ) -> Result<RefineTree, CheckerError> {
        let bb_envs = bb_envs_infer
            .into_iter()
            .map(|(bb, bb_env_infer)| (bb, bb_env_infer.into_bb_env(kvars)))
            .collect();

        dbg::check_span!(genv.tcx, def_id, bb_envs).in_scope(|| {
            let mut refine_tree = RefineTree::new();

            Checker::run(genv, &mut refine_tree, body, def_id, Check { bb_envs, kvars })?;

            Ok(refine_tree)
        })
    }
}

impl<'a, 'tcx, P: Phase> Checker<'a, 'tcx, P> {
    fn run(
        genv: &'a GlobalEnv<'a, 'tcx>,
        refine_tree: &mut RefineTree,
        body: &'a Body<'tcx>,
        def_id: DefId,
        phase: P,
    ) -> Result<(), CheckerError> {
        let mut rcx = refine_tree.refine_ctxt_at_root();

        let fn_sig = genv
            .lookup_fn_sig(def_id)
            .unwrap_or_else(|_| panic!("checking function with unsupported signature"))
            .fn_sig
            .replace_bvars_with_fresh_fvars(|sort| rcx.define_var(sort));

        let env = Self::init(&mut rcx, body, &fn_sig);

        let dominators = body.dominators();
        let mut ck = Checker::new(
            genv,
            body,
            fn_sig.ret().clone(),
            fn_sig.ensures().clone(),
            &dominators,
            phase,
        );

        ck.check_goto(rcx, env, None, START_BLOCK)?;
        while let Some(bb) = ck.queue.pop() {
            let snapshot = ck.snapshot_at_dominator(bb);
            if ck.visited.contains(bb) {
                refine_tree.clear(snapshot);
                ck.clear(bb);
            }

            let snapshot = ck.snapshot_at_dominator(bb);
            let mut rcx = refine_tree.refine_ctxt_at(snapshot).unwrap();
            let mut env = ck.phase.enter_basic_block(&mut rcx, bb);
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
                    assert!(path.projection().is_empty());
                    let ty = rcx.unpack(ty);
                    env.alloc_universal_loc(path.loc, ty);
                }
                rty::Constraint::Pred(e) => {
                    rcx.assume_pred(e.clone());
                }
            }
        }

        for (local, ty) in body.args_iter().zip(fn_sig.args()) {
            let ty = rcx.unpack_with(ty, UnpackFlags::INVARIANTS);
            env.alloc_with_ty(local, ty);
        }

        for local in body.vars_and_temps_iter() {
            env.alloc(local);
        }

        env.alloc(RETURN_PLACE);
        env
    }

    fn clear(&mut self, root: BasicBlock) {
        // TODO(nilehmann) there should be a better way to iterate over all dominated blocks.
        self.visited.remove(root);
        for bb in self.body.basic_blocks.indices() {
            if bb != root && self.dominators.is_dominated_by(bb, root) {
                self.phase.clear(bb);
                self.visited.remove(bb);
            }
        }
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
        let mut latest_src_info = None;
        for stmt in &data.statements {
            dbg::statement!("start", stmt, rcx, env);
            self.check_statement(&mut rcx, &mut env, stmt)?;
            dbg::statement!("end", stmt, rcx, env);
            if !stmt.is_nop() {
                latest_src_info = Some(stmt.source_info);
            }
        }

        if let Some(terminator) = &data.terminator {
            dbg::terminator!("start", terminator, rcx, env);
            let successors =
                self.check_terminator(&mut rcx, &mut env, terminator, latest_src_info)?;
            dbg::terminator!("end", terminator, rcx, env);

            self.snapshots[bb] = Some(rcx.snapshot());
            let term_source_info = match latest_src_info {
                Some(src_info) => src_info,
                None => terminator.source_info,
            };
            self.check_successors(rcx, env, term_source_info, successors)?;
        }
        Ok(())
    }

    fn check_statement(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt: &Statement,
    ) -> Result<(), CheckerError> {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rcx, env, stmt.source_info, rvalue)?;
                let ty = rcx.unpack(&ty);
                let gen =
                    &mut self
                        .phase
                        .constr_gen(self.genv, rcx, Tag::Assign(stmt.source_info.span));
                env.write_place(rcx, gen, place, ty, Some(stmt.source_info))
                    .map_err(|err| CheckerError::from(err).with_src_info(stmt.source_info))?;
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
        src_info: Option<SourceInfo>,
    ) -> Result<Vec<(BasicBlock, Guard)>, CheckerError> {
        match &terminator.kind {
            TerminatorKind::Return => self.check_ret(rcx, env, src_info),
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.check_operand(rcx, env, terminator.source_info, discr)?;
                if discr_ty.is_integral() || discr_ty.is_bool() {
                    Ok(Self::check_if(&discr_ty, targets))
                } else {
                    Ok(Self::check_match(&discr_ty, targets))
                }
            }
            TerminatorKind::Call { func, substs, args, destination, target, instance, .. } => {
                let (func_id, substs) = match instance {
                    Some(inst) => (inst.impl_f, &inst.substs),
                    None => (*func, &substs.lowered),
                };
                let fn_sig = self
                    .genv
                    .lookup_fn_sig(func_id)
                    .map_err(|err| CheckerError::from(err).with_src_info(terminator.source_info))?;

                let ret =
                    self.check_call(rcx, env, terminator.source_info, fn_sig, substs, args)?;

                let ret = rcx.unpack(&ret);
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Call(terminator.source_info.span));
                env.write_place(rcx, &mut gen, destination, ret, Some(terminator.source_info))
                    .map_err(|err| CheckerError::from(err).with_src_info_opt(src_info))?;

                if let Some(target) = target {
                    Ok(vec![(*target, Guard::None)])
                } else {
                    Ok(vec![])
                }
            }
            TerminatorKind::Assert { cond, expected, target, msg } => {
                Ok(vec![(
                    *target,
                    self.check_assert(rcx, env, terminator.source_info, cond, *expected, msg)?,
                )])
            }
            TerminatorKind::Drop { place, target, .. } => {
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Fold(terminator.source_info.span));
                let _ = env.move_place(rcx, &mut gen, place, Some(terminator.source_info));
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::DropAndReplace { place, value, target, .. } => {
                let ty = self.check_operand(rcx, env, terminator.source_info, value)?;
                let ty = rcx.unpack(&ty);
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Assign(terminator.source_info.span));
                env.write_place(rcx, &mut gen, place, ty, Some(terminator.source_info))
                    .map_err(|err| CheckerError::from(err).with_src_info_opt(src_info))?;
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::FalseEdge { real_target, .. } => Ok(vec![(*real_target, Guard::None)]),
            TerminatorKind::FalseUnwind { real_target, .. } => {
                Ok(vec![(*real_target, Guard::None)])
            }
            TerminatorKind::Resume => todo!("implement checking of cleanup code"),
        }
    }

    fn check_ret(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: Option<SourceInfo>,
    ) -> Result<Vec<(BasicBlock, Guard)>, CheckerError> {
        let tag = match src_info {
            Some(info) => Tag::RetAt(info.span),
            None => Tag::Ret,
        };
        let gen = &mut self.phase.constr_gen(self.genv, rcx, tag);
        let ret_place_ty = env
            .lookup_place(rcx, gen, Place::RETURN, src_info)
            .map_err(|err| CheckerError::from(err).with_src_info_opt(src_info))?;

        gen.subtyping(rcx, &ret_place_ty, &self.ret);

        for constraint in &self.ensures {
            gen.check_constraint(rcx, env, constraint, src_info)
                .map_err(|err| CheckerError::from(err).with_src_info_opt(src_info))?;
        }
        Ok(vec![])
    }

    fn check_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        fn_sig: PolySig,
        substs: &[rustc::ty::GenericArg],
        args: &[Operand],
    ) -> Result<Ty, CheckerError> {
        let actuals: Vec<Ty> = args
            .iter()
            .map(|op| self.check_operand(rcx, env, src_info, op))
            .try_collect()?;

        let substs = substs
            .iter()
            .map(|arg| {
                self.genv
                    .refine_generic_arg(arg, &mut |sorts| Binders::new(Expr::hole(), sorts))
            })
            .collect_vec();

        let output = self
            .phase
            .constr_gen(self.genv, rcx, Tag::Call(src_info.span))
            .check_fn_call(rcx, env, &fn_sig, &substs, &actuals, src_info)
            .map_err(|err| err.with_src_info(src_info))?;

        for constr in &output.ensures {
            match constr {
                Constraint::Type(path, updated_ty) => {
                    let updated_ty = rcx.unpack(updated_ty);
                    env.update_path(path, updated_ty);
                }
                Constraint::Pred(e) => rcx.assume_pred(e.clone()),
            }
        }
        Ok(output.ret)
    }

    fn check_assert(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        cond: &Operand,
        expected: bool,
        msg: &AssertKind,
    ) -> Result<Guard, CheckerError> {
        let ty = self.check_operand(rcx, env, source_info, cond)?;
        let pred = if let TyKind::Indexed(BaseTy::Bool, idxs) = ty.kind() {
            if expected {
                idxs.nth(0).as_expr().clone()
            } else {
                idxs.nth(0).as_expr().not()
            }
        } else {
            unreachable!("unexpected ty `{ty:?}`")
        };

        match msg {
            AssertKind::BoundsCheck => {
                self.phase
                    .constr_gen(self.genv, rcx, Tag::Assert("bounds check", source_info.span))
                    .check_pred(rcx, pred.clone());
                Ok(Guard::Pred(pred))
            }
            AssertKind::Other(assert_msg) => {
                match self.genv.check_asserts() {
                    AssertBehavior::Ignore => Ok(Guard::None),
                    AssertBehavior::Assume => Ok(Guard::Pred(pred)),
                    AssertBehavior::Check => {
                        self.phase
                            .constr_gen(self.genv, rcx, Tag::Assert(assert_msg, source_info.span))
                            .check_pred(rcx, pred.clone());

                        Ok(Guard::Pred(pred))
                    }
                }
            }
        }
    }

    fn check_if(discr_ty: &Ty, targets: &rustc_mir::SwitchTargets) -> Vec<(BasicBlock, Guard)> {
        let mk = |bits| {
            match discr_ty.kind() {
                TyKind::Indexed(BaseTy::Bool, idxs) => {
                    if bits == 0 {
                        idxs.nth(0).as_expr().not()
                    } else {
                        idxs.nth(0).as_expr().clone()
                    }
                }
                TyKind::Indexed(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), idxs) => {
                    Expr::binary_op(
                        BinOp::Eq,
                        idxs.nth(0).as_expr().clone(),
                        Expr::from_bits(bty, bits),
                    )
                }
                _ => unreachable!("unexpected discr_ty {:?}", discr_ty),
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
            successors
                .push((targets.otherwise(), Guard::Match(place.clone(), VariantIdx::from_usize(i))))
        } else {
            successors.push((targets.otherwise(), Guard::None));
        }

        successors
    }

    fn check_successors(
        &mut self,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        src_info: SourceInfo,
        successors: Vec<(BasicBlock, Guard)>,
    ) -> Result<(), CheckerError> {
        for (target, guard) in successors {
            let mut rcx = rcx.breadcrumb();
            let mut env = env.clone();
            match guard {
                Guard::None => {}
                Guard::Pred(expr) => {
                    rcx.assume_pred(expr);
                }
                Guard::Match(place, variant_idx) => {
                    env.downcast(self.genv, &mut rcx, &place, variant_idx, src_info)
                        .map_err(|err| CheckerError::from(err).with_src_info(src_info))?;
                }
            }
            self.check_goto(rcx, env, Some(src_info), target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<(), CheckerError> {
        if self.is_exit_block(target) {
            self.check_ret(&mut rcx, &mut env, src_info)?;
            Ok(())
        } else if self.body.is_join_point(target) {
            if P::check_goto_join_point(self, rcx, env, src_info, target)? {
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
        src_info: SourceInfo,
        rvalue: &Rvalue,
    ) -> Result<Ty, CheckerError> {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(rcx, env, src_info, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(rcx, env, src_info, *bin_op, op1, op2)
            }
            Rvalue::MutRef(place) => {
                let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
                env.borrow(rcx, gen, RefKind::Mut, place, src_info)
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))
            }
            Rvalue::ShrRef(place) => {
                let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
                env.borrow(rcx, gen, RefKind::Shr, place, src_info)
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(rcx, env, src_info, *un_op, op),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let sig = self
                    .genv
                    .variant_sig(*def_id, *variant_idx)
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))?;
                self.check_call(rcx, env, src_info, sig, substs, args)
            }
            Rvalue::Aggregate(AggregateKind::Array(ty), args) => {
                let val = args.len();
                let args: Vec<Ty> = args
                    .iter()
                    .map(|op| self.check_operand(rcx, env, src_info, op))
                    .try_collect()?;

                let ty = self
                    .genv
                    .refine_ty(ty, &mut |sorts| self.phase.fresh_kvar(sorts, KVarEncoding::Conj));
                let mut gen = self.phase.constr_gen(self.genv, rcx, Tag::Other);
                for arg in args {
                    gen.subtyping(rcx, &arg, &ty);
                }

                Ok(Ty::array(ty, Const { val }))
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                let tys: Vec<Ty> = args
                    .iter()
                    .map(|op| self.check_operand(rcx, env, src_info, op))
                    .try_collect()?;
                Ok(Ty::tuple(tys))
            }
            Rvalue::Discriminant(place) => {
                let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
                let ty = env
                    .lookup_place(rcx, gen, place, Some(src_info))
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))?;
                let (adt_def, ..) = ty.expect_adt();
                Ok(Ty::discr(adt_def.clone(), place.clone()))
            }
            Rvalue::Len(place) => self.check_len(rcx, env, src_info, place),
            Rvalue::Cast(kind, op, to) => {
                let from = self.check_operand(rcx, env, src_info, op)?;
                Ok(self.check_cast(*kind, &from, to))
            }
        }
    }

    fn check_len(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        place: &Place,
    ) -> Result<Ty, CheckerError> {
        let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
        let ty = env
            .lookup_place(rcx, gen, place, Some(src_info))
            .map_err(|err| CheckerError::from(err).with_src_info(src_info))?;

        let idxs = match ty.kind() {
            TyKind::Array(_, len) => RefineArgs::one(Expr::constant(rty::Constant::from(len.val))),
            TyKind::Indexed(BaseTy::Slice(_), idxs) => idxs.clone(),
            _ => panic!("expected array or slice type"),
        };

        Ok(Ty::indexed(BaseTy::Uint(UintTy::Usize), idxs))
    }

    fn check_binary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        bin_op: mir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Result<Ty, CheckerError> {
        let ty1 = self.check_operand(rcx, env, source_info, op1)?;
        let ty2 = self.check_operand(rcx, env, source_info, op2)?;

        match bin_op {
            mir::BinOp::Eq
            | mir::BinOp::Ne
            | mir::BinOp::Gt
            | mir::BinOp::Ge
            | mir::BinOp::Lt
            | mir::BinOp::Le => Ok(self.check_cmp_op(rcx, source_info, bin_op, &ty1, &ty2)),
            mir::BinOp::Add
            | mir::BinOp::Sub
            | mir::BinOp::Mul
            | mir::BinOp::Div
            | mir::BinOp::BitAnd
            | mir::BinOp::Rem => Ok(self.check_arith_op(rcx, source_info, bin_op, &ty1, &ty2)),
        }
    }

    fn check_arith_op(
        &mut self,
        rcx: &mut RefineCtxt,
        source_info: SourceInfo,
        op: mir::BinOp,
        ty1: &Ty,
        ty2: &Ty,
    ) -> Ty {
        let (bty, idx1, idx2, sig) = match (ty1.kind(), ty2.kind()) {
            (Int!(int_ty1, idxs1), Int!(int_ty2, idxs2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (BaseTy::Int(*int_ty1), idxs1.nth(0), idxs2.nth(0), sigs::signed_bin_ops(op))
            }
            (Uint!(uint_ty1, idxs1), Uint!(uint_ty2, idxs2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (BaseTy::Uint(*uint_ty1), idxs1.nth(0), idxs2.nth(0), sigs::unsigned_bin_ops(op))
            }
            (Bool!(idxs1), Bool!(idxs2)) => {
                (BaseTy::Bool, idxs1.nth(0), idxs2.nth(0), sigs::bool_bin_ops(op))
            }
            (Float!(float_ty1, _), Float!(float_ty2, _)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                return Ty::float(*float_ty1);
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        let (e1, e2) = (idx1.as_expr().clone(), idx2.as_expr().clone());
        if let sigs::Pre::Some(tag, constr) = sig.pre {
            self.phase
                .constr_gen(self.genv, rcx, tag(source_info.span))
                .check_pred(rcx, constr([e1.clone(), e2.clone()]));
        }

        match sig.out {
            sigs::Output::Indexed(mk) => Ty::indexed(bty, RefineArgs::one(mk([e1, e2]))),
            sigs::Output::Exists(mk) => {
                let pred = mk(Expr::nu(), [e1, e2]);
                Ty::exists(bty, Binders::new(pred, vec![Sort::Int]))
            }
        }
    }

    fn check_cmp_op(
        &mut self,
        rcx: &mut RefineCtxt,
        source_info: SourceInfo,
        op: mir::BinOp,
        ty1: &Ty,
        ty2: &Ty,
    ) -> Ty {
        let (idx1, idx2, sig) = match (ty1.kind(), ty2.kind()) {
            (Int!(int_ty1, idxs1), Int!(int_ty2, idxs2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (idxs1.nth(0), idxs2.nth(0), sigs::signed_bin_ops(op))
            }
            (Uint!(uint_ty1, idxs1), Uint!(uint_ty2, idxs2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (idxs1.nth(0), idxs2.nth(0), sigs::unsigned_bin_ops(op))
            }
            (Bool!(idxs1), Bool!(idxs2)) => (idxs1.nth(0), idxs2.nth(0), sigs::bool_bin_ops(op)),
            _ => return Ty::bool(),
        };
        let (e1, e2) = (idx1.as_expr().clone(), idx2.as_expr().clone());
        if let sigs::Pre::Some(tag, constr) = sig.pre {
            self.phase
                .constr_gen(self.genv, rcx, tag(source_info.span))
                .check_pred(rcx, constr([e1.clone(), e2.clone()]));
        }

        let bty = BaseTy::Bool;
        match sig.out {
            sigs::Output::Indexed(mk) => Ty::indexed(bty, RefineArgs::one(mk([e1, e2]))),
            sigs::Output::Exists(mk) => {
                let pred = mk(Expr::nu(), [e1, e2]);
                Ty::exists(bty, Binders::new(pred, vec![Sort::Bool]))
            }
        }
    }

    fn check_unary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        un_op: mir::UnOp,
        op: &Operand,
    ) -> Result<Ty, CheckerError> {
        let ty = self.check_operand(rcx, env, src_info, op)?;
        let ty = match un_op {
            mir::UnOp::Not => {
                if let Bool!(idxs) = ty.kind() {
                    Ty::indexed(BaseTy::Bool, RefineArgs::one(idxs.nth(0).as_expr().not()))
                } else {
                    unreachable!("incompatible type: `{:?}`", ty)
                }
            }
            mir::UnOp::Neg => {
                match ty.kind() {
                    Int!(int_ty, idxs) => {
                        Ty::indexed(
                            BaseTy::Int(*int_ty),
                            RefineArgs::one(idxs.nth(0).as_expr().neg()),
                        )
                    }
                    Float!(float_ty, _) => Ty::float(*float_ty),
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
        };
        Ok(ty)
    }

    fn check_cast(&self, kind: CastKind, from: &Ty, to: &rustc::ty::Ty) -> Ty {
        use rustc::ty::TyKind as RustTy;
        match kind {
            CastKind::IntToInt => {
                match (from.kind(), to.kind()) {
                    (Bool!(idxs), RustTy::Int(int_ty)) => {
                        bool_int_cast(idxs.nth(0).as_expr(), *int_ty)
                    }
                    (Bool!(idxs), RustTy::Uint(uint_ty)) => {
                        bool_uint_cast(idxs.nth(0).as_expr(), *uint_ty)
                    }
                    (Int!(int_ty1, idxs), RustTy::Int(int_ty2)) => {
                        int_int_cast(idxs.nth(0).as_expr(), *int_ty1, *int_ty2)
                    }
                    (Uint!(uint_ty1, idxs), RustTy::Uint(uint_ty2)) => {
                        uint_uint_cast(idxs.nth(0).as_expr(), *uint_ty1, *uint_ty2)
                    }
                    (Uint!(uint_ty, idxs), RustTy::Int(int_ty)) => {
                        uint_int_cast(idxs.nth(0).as_expr(), *uint_ty, *int_ty)
                    }
                    (Int!(_, _), RustTy::Uint(uint_ty)) => Ty::uint(*uint_ty),
                    _ => {
                        panic!("invalid int to int cast")
                    }
                }
            }
            CastKind::FloatToInt | CastKind::IntToFloat => {
                self.genv
                    .refine_ty(to, &mut |sorts| Binders::new(Expr::tt(), sorts))
            }
        }
    }

    fn check_operand(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        operand: &Operand,
    ) -> Result<Ty, CheckerError> {
        let ty = match operand {
            Operand::Copy(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self
                    .phase
                    .constr_gen(self.genv, rcx, Tag::Fold(src_info.span));
                env.lookup_place(rcx, gen, p, Some(src_info))
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))?
            }
            Operand::Move(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self
                    .phase
                    .constr_gen(self.genv, rcx, Tag::Fold(src_info.span));
                env.move_place(rcx, gen, p, Some(src_info))
                    .map_err(|err| CheckerError::from(err).with_src_info(src_info))?
            }
            Operand::Constant(c) => Self::check_constant(c),
        };
        Ok(rcx.unpack(&ty))
    }

    fn check_constant(c: &Constant) -> Ty {
        match c {
            Constant::Int(n, int_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ty::indexed(BaseTy::Int(*int_ty), RefineArgs::one(idx))
            }
            Constant::Uint(n, uint_ty) => {
                let idx = Expr::constant(rty::Constant::from(*n));
                Ty::indexed(BaseTy::Uint(*uint_ty), RefineArgs::one(idx))
            }
            Constant::Bool(b) => {
                let idx = Expr::constant(rty::Constant::from(*b));
                Ty::indexed(BaseTy::Bool, RefineArgs::one(idx))
            }
            Constant::Float(_, float_ty) => Ty::float(*float_ty),
            Constant::Unit => Ty::unit(),
            Constant::Str => Ty::mk_ref(RefKind::Shr, Ty::str()),
            Constant::Char => Ty::char(),
        }
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
    }
}

fn bool_int_cast(b: &Expr, int_ty: IntTy) -> Ty {
    let idx = Expr::ite(b, 1, 0);
    Ty::indexed(BaseTy::Int(int_ty), RefineArgs::one(idx))
}

fn bool_uint_cast(b: &Expr, uint_ty: UintTy) -> Ty {
    let idx = Expr::ite(b, 1, 0);
    Ty::indexed(BaseTy::Uint(uint_ty), RefineArgs::one(idx))
}

fn int_int_cast(idx: &Expr, int_ty1: IntTy, int_ty2: IntTy) -> Ty {
    if int_bit_width(int_ty1) <= int_bit_width(int_ty2) {
        Ty::indexed(BaseTy::Int(int_ty2), RefineArgs::one(idx))
    } else {
        Ty::int(int_ty2)
    }
}

fn uint_int_cast(idx: &Expr, uint_ty: UintTy, int_ty: IntTy) -> Ty {
    if uint_bit_width(uint_ty) < int_bit_width(int_ty) {
        Ty::indexed(BaseTy::Int(int_ty), RefineArgs::one(idx))
    } else {
        Ty::int(int_ty)
    }
}

fn uint_uint_cast(idx: &Expr, uint_ty1: UintTy, uint_ty2: UintTy) -> Ty {
    if uint_bit_width(uint_ty1) <= uint_bit_width(uint_ty2) {
        Ty::indexed(BaseTy::Uint(uint_ty2), RefineArgs::one(idx))
    } else {
        Ty::uint(uint_ty2)
    }
}

fn uint_bit_width(uint_ty: UintTy) -> u64 {
    uint_ty.bit_width().unwrap_or(CONFIG.pointer_width)
}

fn int_bit_width(int_ty: IntTy) -> u64 {
    int_ty.bit_width().unwrap_or(CONFIG.pointer_width)
}

impl Phase for Inference<'_> {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        _rcx: &RefineCtxt,
        tag: Tag,
    ) -> ConstrGen<'a, 'tcx> {
        ConstrGen::new(genv, |sorts: &[Sort], _| Binders::new(Expr::hole(), sorts), tag)
    }

    fn enter_basic_block(&mut self, _rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter()
    }

    fn check_goto_join_point(
        ck: &mut Checker<Inference>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<bool, CheckerError> {
        // TODO(nilehmann) we should only ask for the scope in the vacant branch
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();

        dbg::infer_goto_enter!(target, env, ck.phase.bb_envs.get(&target));
        let mut gen = ConstrGen::new(
            ck.genv,
            |sorts: &[Sort], _| Binders::new(Expr::hole(), sorts),
            Tag::Other,
        );
        let modified = match ck.phase.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(&mut rcx, &mut gen, env, src_info),
            Entry::Vacant(entry) => {
                entry.insert(env.into_infer(&mut rcx, &mut gen, scope));
                true
            }
        };
        dbg::infer_goto_exit!(target, ck.phase.bb_envs[&target]);

        Ok(modified)
    }

    fn fresh_kvar(&mut self, sorts: &[Sort], _: KVarEncoding) -> Binders<Expr> {
        Binders::new(Expr::hole(), sorts)
    }

    fn clear(&mut self, bb: BasicBlock) {
        self.bb_envs.remove(&bb);
    }
}

impl Phase for Check<'_> {
    fn constr_gen<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &RefineCtxt,
        tag: Tag,
    ) -> ConstrGen<'a, 'tcx> {
        let scope = rcx.scope();
        let kvar_gen =
            move |sorts: &[Sort], encoding| self.kvars.fresh(sorts, scope.iter(), encoding);
        ConstrGen::new(genv, kvar_gen, tag)
    }

    fn enter_basic_block(&mut self, rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter(rcx)
    }

    fn check_goto_join_point(
        ck: &mut Checker<Check>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<bool, CheckerError> {
        let bb_env = &ck.phase.bb_envs[&target];
        debug_assert_eq!(&ck.snapshot_at_dominator(target).scope().unwrap(), bb_env.scope());

        dbg::check_goto!(target, rcx, env, bb_env);

        let kvar_gen =
            |sorts: &[Sort], encoding| ck.phase.kvars.fresh(sorts, bb_env.scope().iter(), encoding);
        let tag = Tag::Goto(src_info.map(|s| s.span), target);
        let gen = &mut ConstrGen::new(ck.genv, kvar_gen, tag);
        env.check_goto(&mut rcx, gen, bb_env, src_info)
            .map_err(|err| CheckerError::from(err).with_src_info_opt(src_info))?;

        Ok(!ck.visited.contains(target))
    }

    fn fresh_kvar(&mut self, sorts: &[Sort], encoding: KVarEncoding) -> Binders<Expr> {
        self.kvars.fresh(sorts, [], encoding)
    }

    fn clear(&mut self, _bb: BasicBlock) {
        unreachable!();
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
        self.dominators.rank_partial_cmp(self.bb, other.bb)
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
    use flux_macros::Diagnostic;
    use flux_middle::{
        global_env::{OpaqueStructErr, UnsupportedFnSig},
        pretty,
        rty::evars::UnsolvedEvar,
    };
    use rustc_errors::IntoDiagnostic;
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir::SourceInfo;
    use rustc_span::Span;

    use crate::param_infer::InferenceError;

    #[derive(Diagnostic)]
    #[diag(refineck::opaque_struct_error, code = "FLUX")]
    pub struct OpaqueStructError {
        #[primary_span]
        pub span: Option<Span>,
    }

    pub struct CheckerError {
        kind: CheckerErrKind,
        span: Option<Span>,
    }

    pub enum CheckerErrKind {
        Inference,
        OpaqueStruct(DefId),
        UnsupportedCall { def_span: Span, reason: String },
    }

    impl CheckerError {
        pub(crate) fn with_src_info_opt(mut self, src_info: Option<SourceInfo>) -> Self {
            if let Some(src_info) = src_info {
                self.span = Some(src_info.span);
            }
            self
        }

        pub(crate) fn with_src_info(mut self, src_info: SourceInfo) -> Self {
            self.span = Some(src_info.span);
            self
        }
    }

    impl<'a> IntoDiagnostic<'a> for CheckerError {
        fn into_diagnostic(
            self,
            handler: &'a rustc_errors::Handler,
        ) -> rustc_errors::DiagnosticBuilder<'a, ErrorGuaranteed> {
            use flux_errors::fluent::refineck;
            let fluent = match &self.kind {
                CheckerErrKind::Inference => refineck::param_inference_error,
                CheckerErrKind::OpaqueStruct(_) => refineck::opaque_struct_error,
                CheckerErrKind::UnsupportedCall { .. } => refineck::unsupported_call,
            };
            let mut builder = handler.struct_err_with_code(fluent, flux_errors::diagnostic_id());
            if let Some(span) = self.span {
                builder.set_span(span);
            }

            match self.kind {
                CheckerErrKind::Inference => {}
                CheckerErrKind::OpaqueStruct(def_id) => {
                    builder.set_arg("struct", pretty::def_id_to_string(def_id));
                }
                CheckerErrKind::UnsupportedCall { def_span, reason } => {
                    builder.span_note(def_span, refineck::function_definition);
                    builder.note(reason);
                }
            }
            builder
        }
    }

    impl From<UnsolvedEvar> for CheckerError {
        fn from(_: UnsolvedEvar) -> Self {
            CheckerError { kind: CheckerErrKind::Inference, span: None }
        }
    }

    impl From<InferenceError> for CheckerError {
        fn from(_: InferenceError) -> Self {
            CheckerError { kind: CheckerErrKind::Inference, span: None }
        }
    }

    impl From<OpaqueStructErr> for CheckerError {
        fn from(OpaqueStructErr(kind): OpaqueStructErr) -> Self {
            CheckerError { kind: CheckerErrKind::OpaqueStruct(kind), span: None }
        }
    }

    impl From<UnsupportedFnSig> for CheckerError {
        fn from(err: UnsupportedFnSig) -> Self {
            CheckerError {
                kind: CheckerErrKind::UnsupportedCall { def_span: err.span, reason: err.reason },
                span: None,
            }
        }
    }
}
