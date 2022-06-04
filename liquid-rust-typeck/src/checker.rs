extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{hash_map::Entry, BinaryHeap};

use itertools::Itertools;

use rustc_data_structures::graph::dominators::Dominators;
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir as rustc_mir;

use liquid_rust_common::{config::AssertBehavior, index::IndexVec};
use liquid_rust_middle::{
    global_env::GlobalEnv,
    rustc::{
        self,
        mir::{
            self, AggregateKind, BasicBlock, Body, Constant, Operand, Place, Rvalue, SourceInfo,
            Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
    },
    ty::{
        self, BaseTy, BinOp, BoundVar, Constr, Constrs, Expr, FnSig, Param, PolySig, Pred, Sort,
        Ty, TyKind,
    },
};

use crate::{
    constraint_gen::{ConstraintGen, FnCallChecker, Tag},
    dbg,
    fixpoint::KVarStore,
    refine_tree::{RefineCtxt, RefineTree, Snapshot},
    type_env::{BasicBlockEnv, TypeEnv, TypeEnvInfer},
};

pub struct Checker<'a, 'tcx, M> {
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    genv: &'a GlobalEnv<'tcx>,
    mode: M,
    ret: Ty,
    ensures: Constrs,
    /// A snapshot of the pure context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: &'a Dominators<BasicBlock>,
    queue: WorkQueue<'a>,
}

pub trait Mode: Sized {
    type KvarGen<'a>: FnMut(&BaseTy) -> Pred
    where
        Self: 'a;

    fn kvar_gen(&mut self, rcx: &RefineCtxt) -> Self::KvarGen<'_>;

    fn fnck<'a, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'tcx>,
        rcx: &'a mut RefineCtxt,
        tag: Tag,
    ) -> FnCallChecker<'a, 'tcx, Self::KvarGen<'_>> {
        FnCallChecker::new(genv, rcx, self.kvar_gen(rcx), tag)
    }

    fn enter_basic_block(&mut self, rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv;

    fn check_goto_join_point(
        ck: &mut Checker<Self>,
        rcx: RefineCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> bool;

    fn clear(&mut self, bb: BasicBlock);
}

pub struct Inference<'a> {
    bb_envs: &'a mut FxHashMap<BasicBlock, TypeEnvInfer>,
}

pub struct Check<'a> {
    bb_envs_infer: FxHashMap<BasicBlock, TypeEnvInfer>,
    bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
    kvars: &'a mut KVarStore,
}

/// A 'Guard' describes extra "control" information that holds at the start
/// of the successor basic block
pub type Guard = Option<Expr>;

impl<'a, 'tcx, M> Checker<'a, 'tcx, M> {
    fn new(
        genv: &'a GlobalEnv<'tcx>,
        body: &'a Body<'tcx>,
        ret: Ty,
        ensures: Constrs,
        dominators: &'a Dominators<BasicBlock>,
        mode: M,
    ) -> Self {
        Checker {
            genv,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            ret,
            ensures,
            mode,
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            dominators,
            queue: WorkQueue::empty(body.basic_blocks.len(), dominators),
        }
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Inference<'_>> {
    pub fn infer(
        genv: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        def_id: DefId,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvInfer>, ErrorReported> {
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
        genv: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        def_id: DefId,
        kvars: &mut KVarStore,
        bb_envs_infer: FxHashMap<BasicBlock, TypeEnvInfer>,
    ) -> Result<RefineTree, ErrorReported> {
        dbg::check_span!(genv.tcx, def_id, bb_envs_infer).in_scope(|| {
            let mut refine_tree = RefineTree::new();

            Checker::run(
                genv,
                &mut refine_tree,
                body,
                def_id,
                Check { bb_envs_infer, bb_envs: FxHashMap::default(), kvars },
            )?;

            Ok(refine_tree)
        })
    }
}

impl<'a, 'tcx, M: Mode> Checker<'a, 'tcx, M> {
    fn run(
        genv: &'a GlobalEnv<'tcx>,
        refine_tree: &mut RefineTree,
        body: &'a Body<'tcx>,
        def_id: DefId,
        mode: M,
    ) -> Result<(), ErrorReported> {
        let mut rcx = refine_tree.refine_ctxt_at_root();

        let fn_sig = genv
            .lookup_fn_sig(def_id)
            .replace_bvars_with_fresh_fvars(|sort| rcx.define_var(sort));

        let env = Self::init(&mut rcx, body, &fn_sig);

        let dominators = body.dominators();
        let mut ck = Checker::new(
            genv,
            body,
            fn_sig.ret().clone(),
            fn_sig.ensures().clone(),
            &dominators,
            mode,
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
            let mut env = ck.mode.enter_basic_block(&mut rcx, bb);
            env.unpack(&mut rcx);
            ck.check_basic_block(rcx, env, bb)?;
        }

        Ok(())
    }

    fn init(rcx: &mut RefineCtxt, body: &Body, fn_sig: &FnSig) -> TypeEnv {
        let mut env = TypeEnv::new();
        for constr in fn_sig.requires() {
            match constr {
                ty::Constr::Type(path, ty) => {
                    let loc = path.to_loc().unwrap();
                    let ty = env.unpack_ty(rcx, ty);
                    env.alloc_with_ty(loc, ty);
                }
                ty::Constr::Pred(e) => {
                    rcx.assume_pred(e.clone());
                }
            }
        }

        for (local, ty) in body.args_iter().zip(fn_sig.args()) {
            let ty = env.unpack_ty(rcx, ty);
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
                self.mode.clear(bb);
                self.visited.remove(bb);
            }
        }
    }

    fn check_basic_block(
        &mut self,
        mut rcx: RefineCtxt,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        dbg::basic_block_start!(bb, rcx, env);

        self.visited.insert(bb);
        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            dbg::statement!("start", stmt, rcx, env);
            self.check_statement(&mut rcx, &mut env, stmt)?;
            dbg::statement!("end", stmt, rcx, env);
        }
        if let Some(terminator) = &data.terminator {
            dbg::terminator!("start", terminator, rcx, env);
            let successors = self.check_terminator(&mut rcx, &mut env, terminator)?;
            dbg::terminator!("end", terminator, rcx, env);

            self.snapshots[bb] = Some(rcx.snapshot());
            self.check_successors(rcx, env, terminator.source_info, successors)?;
        }
        Ok(())
    }

    fn check_statement(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        stmt: &Statement,
    ) -> Result<(), ErrorReported> {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rcx, env, stmt.source_info, rvalue)?;
                let ty = env.unpack_ty(rcx, &ty);
                let fresh_kvar = self.mode.kvar_gen(rcx);
                env.write_place(
                    self.genv,
                    rcx,
                    fresh_kvar,
                    place,
                    ty,
                    Tag::Assign(stmt.source_info.span),
                );
            }
            StatementKind::SetDiscriminant { .. } => {
                // TODO(nilehmann) double chould check here that the place is unfolded to
                // the corect variant. This should be guaranteed by rustc
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

    /// For `check_terminator`, the output Vec<BasicBlock, Guard> denotes,
    /// - `BasicBlock` "successors" of the current terminator, and
    /// - `Option<Expr>` are extra guard information from, e.g. the SwitchInt (or Assert ) case t
    ///    that is some predicate you can assume when checking the correspondnig successor.
    fn check_terminator(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        terminator: &Terminator,
    ) -> Result<Vec<(BasicBlock, Guard)>, ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => self.check_ret(rcx, env),
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                self.check_switch_int(rcx, env, discr, targets)
            }
            TerminatorKind::Call { func, substs, args, destination, .. } => {
                let fn_sig = self.genv.lookup_fn_sig(*func);
                let ret =
                    self.check_call(rcx, env, terminator.source_info, fn_sig, substs, args)?;
                if let Some((p, bb)) = destination {
                    let ret = env.unpack_ty(rcx, &ret);
                    let fresh_kvar = self.mode.kvar_gen(rcx);
                    env.write_place(
                        self.genv,
                        rcx,
                        fresh_kvar,
                        p,
                        ret,
                        Tag::Call(terminator.source_info.span),
                    );
                    Ok(vec![(*bb, Guard::None)])
                } else {
                    Ok(vec![])
                }
            }
            TerminatorKind::Assert { cond, expected, target, msg } => {
                Ok(vec![(
                    *target,
                    self.check_assert(rcx, env, terminator.source_info, cond, *expected, msg),
                )])
            }
            TerminatorKind::Drop { place, target, .. } => {
                let mut fnck = self.mode.fnck(self.genv, rcx, Tag::Ret);
                let _ = env.move_place(&mut fnck, place);
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::DropAndReplace { place, value, target, .. } => {
                let ty = self.check_operand(rcx, env, value);
                let ty = env.unpack_ty(rcx, &ty);
                let fresh_kvar = self.mode.kvar_gen(rcx);
                env.write_place(
                    self.genv,
                    rcx,
                    fresh_kvar,
                    place,
                    ty,
                    Tag::Assign(terminator.source_info.span),
                );
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
    ) -> Result<Vec<(BasicBlock, Guard)>, ErrorReported> {
        let ret_place_ty =
            env.lookup_place(&mut self.mode.fnck(self.genv, rcx, Tag::Ret), Place::RETURN);
        let mut gen = ConstraintGen::new(self.genv, rcx, Tag::Ret);

        gen.subtyping(&ret_place_ty, &self.ret);

        for constr in &self.ensures {
            gen.check_constr(env, constr);
        }
        Ok(vec![])
    }

    fn check_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        fn_sig: PolySig,
        substs: &[rustc::ty::GenericArg],
        args: &[Operand],
    ) -> Result<Ty, ErrorReported> {
        let actuals = args
            .iter()
            .map(|op| self.check_operand(rcx, env, op))
            .collect_vec();

        let substs = substs
            .iter()
            .map(|arg| self.genv.refine_generic_arg(arg, &mut |_| Pred::Hole))
            .collect_vec();

        let fresh_kvar = self.mode.kvar_gen(rcx);

        let output = FnCallChecker::new(self.genv, rcx, fresh_kvar, Tag::Call(source_info.span))
            .check(env, &fn_sig, &substs, &actuals)
            .map_err(|_| {
                self.genv
                    .tcx
                    .sess
                    .emit_err(errors::ParamInferenceError { span: source_info.span })
            })?;

        for constr in &output.ensures {
            match constr {
                Constr::Type(path, updated_ty) => {
                    let updated_ty = env.unpack_ty(rcx, updated_ty);
                    env.update_path(&path.expect_path(), updated_ty);
                }
                Constr::Pred(e) => rcx.assume_pred(e.clone()),
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
        msg: &'static str,
    ) -> Guard {
        let ty = self.check_operand(rcx, env, cond);
        let pred = if let TyKind::Indexed(BaseTy::Bool, indices) = ty.kind() {
            if expected {
                indices[0].expr.clone()
            } else {
                indices[0].expr.not()
            }
        } else {
            unreachable!("unexpected ty `{ty:?}`")
        };

        match self.genv.check_asserts() {
            AssertBehavior::Ignore => None,
            AssertBehavior::Assume => Some(pred),
            AssertBehavior::Check => {
                let mut gen =
                    ConstraintGen::new(self.genv, rcx, Tag::Assert(msg, source_info.span));
                gen.check_pred(pred.clone());

                Some(pred)
            }
        }
    }

    fn check_switch_int(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        discr: &Operand,
        targets: &rustc_mir::SwitchTargets,
    ) -> Result<Vec<(BasicBlock, Guard)>, ErrorReported> {
        let discr_ty = self.check_operand(rcx, env, discr);
        let mk = |bits| {
            match discr_ty.kind() {
                TyKind::Indexed(BaseTy::Bool, indices) => {
                    if bits == 0 {
                        indices[0].expr.not()
                    } else {
                        indices[0].expr.clone()
                    }
                }
                TyKind::Indexed(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), indices) => {
                    Expr::binary_op(BinOp::Eq, indices[0].clone(), Expr::from_bits(bty, bits))
                }
                TyKind::Discr => Expr::tt(),
                _ => unreachable!("unexpected discr_ty {:?}", discr_ty),
            }
        };

        let mut successors = vec![];

        for (bits, bb) in targets.iter() {
            successors.push((bb, Some(mk(bits))));
        }
        let otherwise = targets
            .iter()
            .map(|(bits, _)| mk(bits).not())
            .reduce(|e1, e2| Expr::binary_op(BinOp::And, e1, e2));
        let otherwise = match otherwise {
            Some(p) => Some(p),
            None => Guard::None,
        };
        successors.push((targets.otherwise(), otherwise));

        Ok(successors)
    }

    fn check_successors(
        &mut self,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        src_info: SourceInfo,
        successors: Vec<(BasicBlock, Guard)>,
    ) -> Result<(), ErrorReported> {
        for (target, guard) in successors {
            let mut rcx = rcx.breadcrumb();
            let env = env.clone();
            if let Some(guard) = guard {
                rcx.assume_pred(guard);
            }
            self.check_goto(rcx, env, Some(src_info), target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        rcx: RefineCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        if self.body.is_join_point(target) {
            if M::check_goto_join_point(self, rcx, env, src_info, target) {
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
        source_info: SourceInfo,
        rvalue: &Rvalue,
    ) -> Result<Ty, ErrorReported> {
        match rvalue {
            Rvalue::Use(operand) => Ok(self.check_operand(rcx, env, operand)),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                Ok(self.check_binary_op(rcx, env, source_info, *bin_op, op1, op2))
            }
            Rvalue::MutRef(place) => {
                Ok(env.borrow_mut(&mut self.mode.fnck(self.genv, rcx, Tag::Ret), place))
            }
            Rvalue::ShrRef(place) => {
                Ok(env.borrow_shr(&mut self.mode.fnck(self.genv, rcx, Tag::Ret), place))
            }
            Rvalue::UnaryOp(un_op, op) => Ok(self.check_unary_op(rcx, env, *un_op, op)),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let sig = self.genv.variant_sig(*def_id, *variant_idx);
                self.check_call(rcx, env, source_info, sig, substs, args)
            }
            Rvalue::Discriminant(_p) => Ok(Ty::discr()),
        }
    }

    fn check_binary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        bin_op: mir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.check_operand(rcx, env, op1);
        let ty2 = self.check_operand(rcx, env, op2);

        match bin_op {
            mir::BinOp::Eq => self.check_eq(BinOp::Eq, &ty1, &ty2),
            mir::BinOp::Ne => self.check_eq(BinOp::Ne, &ty1, &ty2),
            mir::BinOp::Add => self.check_arith_op(rcx, source_info, BinOp::Add, &ty1, &ty2),
            mir::BinOp::Sub => self.check_arith_op(rcx, source_info, BinOp::Sub, &ty1, &ty2),
            mir::BinOp::Mul => self.check_arith_op(rcx, source_info, BinOp::Mul, &ty1, &ty2),
            mir::BinOp::Div => self.check_arith_op(rcx, source_info, BinOp::Div, &ty1, &ty2),
            mir::BinOp::Rem => self.check_rem(rcx, source_info, &ty1, &ty2),
            mir::BinOp::Gt => self.check_cmp_op(BinOp::Gt, &ty1, &ty2),
            mir::BinOp::Ge => self.check_cmp_op(BinOp::Ge, &ty1, &ty2),
            mir::BinOp::Lt => self.check_cmp_op(BinOp::Lt, &ty1, &ty2),
            mir::BinOp::Le => self.check_cmp_op(BinOp::Le, &ty1, &ty2),
            mir::BinOp::BitAnd => self.check_bitwise_op(BinOp::And, &ty1, &ty2),
        }
    }

    fn check_bitwise_op(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), _),
                TyKind::Indexed(BaseTy::Int(int_ty2), _),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                Ty::exists(BaseTy::Int(*int_ty1), Pred::tt())
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), _),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), _),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                Ty::exists(BaseTy::Uint(*uint_ty1), Pred::tt())
            }
            (TyKind::Indexed(BaseTy::Bool, indices1), TyKind::Indexed(BaseTy::Bool, indices2)) => {
                let e = Expr::binary_op(op, indices1[0].expr.clone(), indices2[0].expr.clone());
                Ty::indexed(BaseTy::Bool, vec![e.into()])
            }
            _ => unreachable!("non-boolean arguments to bitwise op: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    // Rem is a special case due to differing semantics with negative numbers
    fn check_rem(&self, rcx: &mut RefineCtxt, source_info: SourceInfo, ty1: &Ty, ty2: &Ty) -> Ty {
        let mut gen = ConstraintGen::new(self.genv, rcx, Tag::Rem(source_info.span));
        let ty = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), exprs1),
                TyKind::Indexed(BaseTy::Int(int_ty2), exprs2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                let (e1, e2) = (&exprs1[0], &exprs2[0]);
                gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

                let bty = BaseTy::Int(*int_ty1);
                let binding = Expr::binary_op(
                    BinOp::Eq,
                    Expr::bvar(BoundVar::NU),
                    Expr::binary_op(BinOp::Mod, e1.clone(), e2.clone()),
                );
                let guard = Expr::binary_op(
                    BinOp::And,
                    Expr::binary_op(BinOp::Ge, e1.clone(), Expr::zero()),
                    Expr::binary_op(BinOp::Ge, e2.clone(), Expr::zero()),
                );
                let pred = Expr::binary_op(BinOp::Imp, guard, binding);
                Ty::exists(bty, pred)
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), indices1),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), indices2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                let (e1, e2) = (&indices1[0].expr, &indices2[0].expr);
                gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

                Ty::indexed(
                    BaseTy::Uint(*uint_ty1),
                    vec![Expr::binary_op(BinOp::Mod, e1.clone(), e2.clone()).into()],
                )
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };

        ty
    }

    fn check_arith_op(
        &self,
        rcx: &mut RefineCtxt,
        source_info: SourceInfo,
        op: BinOp,
        ty1: &Ty,
        ty2: &Ty,
    ) -> Ty {
        let (bty, e1, e2) = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), indices1),
                TyKind::Indexed(BaseTy::Int(int_ty2), indices2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (BaseTy::Int(*int_ty1), indices1[0].expr.clone(), indices2[0].expr.clone())
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), indices1),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), indices2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (BaseTy::Uint(*uint_ty1), indices1[0].expr.clone(), indices2[0].expr.clone())
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                return Ty::float(*float_ty1);
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        if matches!(op, BinOp::Div) {
            let mut gen = ConstraintGen::new(self.genv, rcx, Tag::Div(source_info.span));
            gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));
        }
        Ty::indexed(bty, vec![Expr::binary_op(op, e1, e2).into()])
    }

    fn check_cmp_op(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        let (e1, e2) = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), indices1),
                TyKind::Indexed(BaseTy::Int(int_ty2), indices2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (indices1[0].expr.clone(), indices2[0].expr.clone())
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), indices1),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), indices2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (indices1[0].expr.clone(), indices2[0].expr.clone())
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                return Ty::exists(BaseTy::Bool, Pred::tt());
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        Ty::indexed(BaseTy::Bool, vec![Expr::binary_op(op, e1, e2).into()])
    }

    fn check_eq(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, indices1), TyKind::Indexed(bty2, indices2)) => {
                debug_assert_eq!(bty1, bty2);
                let e = Expr::binary_op(op, indices1[0].clone(), indices2[0].clone());
                Ty::indexed(BaseTy::Bool, vec![e.into()])
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ty::exists(BaseTy::Bool, Pred::tt())
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_unary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        un_op: mir::UnOp,
        op: &Operand,
    ) -> Ty {
        let ty = self.check_operand(rcx, env, op);
        match un_op {
            mir::UnOp::Not => {
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Bool, indices) => {
                        Ty::indexed(BaseTy::Bool, vec![indices[0].expr.not().into()])
                    }
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
            mir::UnOp::Neg => {
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Int(int_ty), indices) => {
                        Ty::indexed(BaseTy::Int(*int_ty), vec![indices[0].expr.neg().into()])
                    }
                    TyKind::Float(float_ty) => Ty::float(*float_ty),
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
        }
    }

    fn check_operand(&mut self, rcx: &mut RefineCtxt, env: &mut TypeEnv, operand: &Operand) -> Ty {
        let ty = match operand {
            Operand::Copy(p) => {
                // OWNERSHIP SAFETY CHECK
                env.lookup_place(&mut self.mode.fnck(self.genv, rcx, Tag::Ret), p)
            }
            Operand::Move(p) => {
                // OWNERSHIP SAFETY CHECK
                env.move_place(&mut self.mode.fnck(self.genv, rcx, Tag::Ret), p)
            }
            Operand::Constant(c) => self.check_constant(c),
        };
        env.unpack_ty(rcx, &ty)
    }

    fn check_constant(&self, c: &Constant) -> Ty {
        match c {
            Constant::Int(n, int_ty) => {
                let idx = Expr::constant(ty::Constant::from(*n)).into();
                Ty::indexed(BaseTy::Int(*int_ty), vec![idx])
            }
            Constant::Uint(n, uint_ty) => {
                let idx = Expr::constant(ty::Constant::from(*n)).into();
                Ty::indexed(BaseTy::Uint(*uint_ty), vec![idx])
            }
            Constant::Bool(b) => {
                let idx = Expr::constant(ty::Constant::from(*b)).into();
                Ty::indexed(BaseTy::Bool, vec![idx])
            }
            Constant::Float(_, float_ty) => Ty::float(*float_ty),
            Constant::Unit => Ty::unit(),
        }
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
    }
}

impl Mode for Inference<'_> {
    type KvarGen<'a>
    where
        Self: 'a,
    = impl FnMut(&BaseTy) -> Pred;

    fn kvar_gen(&mut self, _rcx: &RefineCtxt) -> Self::KvarGen<'_> {
        |_| Pred::Hole
    }

    fn enter_basic_block(&mut self, rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter(rcx)
    }

    fn check_goto_join_point(
        ck: &mut Checker<Inference>,
        _rcx: RefineCtxt,
        env: TypeEnv,
        _src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> bool {
        // TODO(nilehmann) we should only ask for the scope in the vacant branch
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();

        dbg::infer_goto_enter!(target, env, ck.mode.bb_envs.get(&target));
        let modified = match ck.mode.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(ck.genv, env),
            Entry::Vacant(entry) => {
                entry.insert(env.into_infer(scope));
                true
            }
        };
        dbg::infer_goto_exit!(target, ck.mode.bb_envs[&target]);

        modified
    }

    fn clear(&mut self, bb: BasicBlock) {
        self.bb_envs.remove(&bb);
    }
}

impl Mode for Check<'_> {
    type KvarGen<'a>
    where
        Self: 'a,
    = impl FnMut(&BaseTy) -> Pred;

    fn kvar_gen(&mut self, rcx: &RefineCtxt) -> Self::KvarGen<'_> {
        let scope = rcx.scope();
        move |bty| {
            let kvars = &mut self.kvars;
            kvars.fresh(bty.sorts(), scope.iter())
        }
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
    ) -> bool {
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();
        let mut first = false;

        let bb_env = match ck.mode.bb_envs.entry(target) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let fresh_kvar = &mut |sorts: &[Sort], params: &[Param]| {
                    ck.mode.kvars.fresh(
                        sorts,
                        scope
                            .iter()
                            .chain(params.iter().map(|param| (param.name, param.sort.clone()))),
                    )
                };
                first = true;
                entry.insert(
                    ck.mode
                        .bb_envs_infer
                        .remove(&target)
                        .unwrap()
                        .into_bb_env(fresh_kvar),
                )
            }
        };

        let fresh_kvar = |bty: &BaseTy| ck.mode.kvars.fresh(bty.sorts(), scope.iter());

        dbg::check_goto!(target, rcx, env, bb_env);

        let tag = Tag::Goto(src_info.map(|s| s.span), target);
        env.check_goto(ck.genv, &mut rcx, fresh_kvar, bb_env, tag);

        first
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

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct ParamInferenceError {
        #[message = "parameter inference error at function call"]
        pub span: Span,
    }
}
