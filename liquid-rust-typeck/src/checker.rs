extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::hash_map::Entry;

use crate::{
    constraint_builder::{ConstraintBuilder, Cursor},
    global_env::GlobalEnv,
    lowering::LoweringCtxt,
    subst::Subst,
    ty::{self, BaseTy, BinOp, Expr, ExprKind, FnSig, Loc, Ty, TyKind, Var},
    type_env::{BasicBlockEnv, TypeEnv},
};
use itertools::Itertools;
use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Operand, Place, Rvalue, SourceInfo, Statement,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
    },
    ty as core,
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir;
use rustc_session::Session;

use super::type_env::TypeEnvShape;

pub struct Checker<'a, 'tcx> {
    sess: &'a Session,
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    global_env: &'a GlobalEnv<'tcx>,
    mode: Mode<'a, 'tcx>,
    fn_sig: FnSig,
}

enum Mode<'a, 'tcx> {
    Inference(&'a mut FxHashMap<BasicBlock, TypeEnv<'tcx>>),
    Check {
        shapes: FxHashMap<BasicBlock, TypeEnvShape>,
        bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
        // Whether the block immediately domminates a join point.
        dominates_join_point: BitSet<BasicBlock>,
    },
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    fn new(
        global_env: &'a GlobalEnv<'tcx>,
        body: &'a Body<'tcx>,
        fn_sig: FnSig,
        mode: Mode<'a, 'tcx>,
    ) -> Checker<'a, 'tcx> {
        Checker {
            sess: global_env.tcx.sess,
            global_env,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            fn_sig,
            mode,
        }
    }

    pub fn infer(
        global_env: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvShape>, ErrorReported> {
        let mut constraint = ConstraintBuilder::new(global_env.tcx);
        let cursor = &mut constraint.as_cursor();
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig, cursor);

        let mut bb_envs = FxHashMap::default();
        let mut checker = Checker::new(global_env, body, fn_sig, Mode::Inference(&mut bb_envs));
        checker.run(cursor)?;

        Ok(bb_envs
            .into_iter()
            .map(|(bb, env)| (bb, env.into_shape()))
            .collect())
    }

    pub fn check(
        global_env: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
        shapes: FxHashMap<BasicBlock, TypeEnvShape>,
    ) -> Result<ConstraintBuilder<'tcx>, ErrorReported> {
        let mut constraint = ConstraintBuilder::new(global_env.tcx);
        let cursor = &mut constraint.as_cursor();
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig, cursor);

        let dominators = body.dominators();
        let mut dominates_join_point = BitSet::new_empty(body.basic_blocks.len());
        for bb in body.join_points() {
            dominates_join_point.insert(dominators.immediate_dominator(bb));
        }

        let mut checker = Checker::new(
            global_env,
            body,
            fn_sig,
            Mode::Check {
                shapes,
                bb_envs: FxHashMap::default(),
                dominates_join_point,
            },
        );
        checker.run(cursor)?;
        Ok(constraint)
    }

    fn run(&mut self, cursor: &mut Cursor) -> Result<(), ErrorReported> {
        let mut env = TypeEnv::new(self.global_env.tcx);

        for param in &self.fn_sig.params {
            cursor.push_forall(param.name, param.sort, param.pred.clone());
        }

        for (loc, ty) in &self.fn_sig.requires {
            env.insert_loc(Loc::Abstract(*loc), cursor.unpack(ty.clone()));
        }

        for (local, ty) in self.body.args_iter().zip(&self.fn_sig.args) {
            env.insert_loc(Loc::Local(local), cursor.unpack(ty.clone()))
        }

        for local in self.body.vars_and_temps_iter() {
            env.insert_loc(Loc::Local(local), TyKind::Uninit.intern())
        }

        env.insert_loc(Loc::Local(RETURN_PLACE), TyKind::Uninit.intern());

        self.check_goto(&mut env, cursor, START_BLOCK)?;
        for bb in self.body.reverse_postorder() {
            if !self.visited.contains(bb) {
                let mut env = self.enter_basic_block(cursor, bb);
                env.unpack(cursor);
                self.check_basic_block(&mut env, cursor, bb)?;
            }
        }

        Ok(())
    }

    fn enter_basic_block(&self, cursor: &mut Cursor, bb: BasicBlock) -> TypeEnv<'tcx> {
        match &self.mode {
            Mode::Inference(bb_envs) => bb_envs[&bb].clone(),
            Mode::Check { bb_envs, .. } => bb_envs[&bb].enter(self.global_env.tcx, cursor),
        }
    }

    fn check_basic_block(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        self.visited.insert(bb);

        if matches!(&self.mode, Mode::Check { dominates_join_point, .. } if dominates_join_point.contains(bb))
        {
            cursor.push_scope();
        }

        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(env, cursor, stmt);
        }
        if let Some(terminator) = &data.terminator {
            self.check_terminator(env, cursor, terminator)?;
        }
        Ok(())
    }

    fn check_statement(&self, env: &mut TypeEnv<'tcx>, cursor: &mut Cursor, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(p, rvalue) => {
                let ty = self.check_rvalue(env, cursor, rvalue);
                let ty = cursor.unpack(ty);
                env.write_place(cursor, p, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        terminator: &Terminator,
    ) -> Result<(), ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = env.lookup_local(RETURN_PLACE);
                cursor.subtyping(ret_place_ty, self.fn_sig.ret.clone());

                for (loc, ensured_ty) in &self.fn_sig.ensures {
                    let actual_ty = env.lookup_loc(Loc::Abstract(*loc)).unwrap();
                    cursor.subtyping(actual_ty, ensured_ty.clone());
                }
            }
            TerminatorKind::Goto { target } => {
                self.check_goto(env, cursor, *target)?;
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.check_switch_int(env, cursor, discr, targets)?;
            }
            TerminatorKind::Call {
                func,
                substs,
                args,
                destination,
            } => {
                self.check_call(
                    env,
                    cursor,
                    terminator.source_info,
                    *func,
                    substs,
                    args,
                    destination,
                )?;
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
            } => {
                self.check_assert(env, cursor, cond, *expected, *target)?;
            }
            TerminatorKind::Drop { place, target } => {
                let _ = env.move_place(place);
                self.check_goto(env, cursor, *target)?;
            }
        }
        Ok(())
    }

    fn check_call(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        source_info: SourceInfo,
        func: DefId,
        substs: &[core::Ty],
        args: &[Operand],
        destination: &Option<(Place, BasicBlock)>,
    ) -> Result<(), ErrorReported> {
        let fn_sig = self.global_env.lookup_fn_sig(func);
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig, cursor);

        let actuals = args
            .iter()
            .map(|arg| self.check_operand(env, arg))
            .collect_vec();

        let cx = LoweringCtxt::empty();
        let mut fresh_kvar = |sort| cursor.fresh_kvar(Var::Bound, sort);
        let substs = substs
            .iter()
            .map(|ty| cx.lower_ty(ty, &mut fresh_kvar))
            .collect();

        let mut subst = Subst::with_type_substs(substs);
        if subst.infer_from_fn_call(env, &actuals, &fn_sig).is_err() {
            return self.report_inference_error(source_info);
        };

        for param in fn_sig.params {
            cursor.push_head(subst.subst_pred(&param.pred));
        }

        for (actual, formal) in actuals.into_iter().zip(&fn_sig.args) {
            cursor.subtyping(actual, subst.subst_ty(formal));
        }

        for (loc, required_ty) in fn_sig.requires {
            let loc = subst.subst_loc(Loc::Abstract(loc));
            let actual_ty = env.lookup_loc(loc).unwrap();
            let required_ty = subst.subst_ty(&required_ty);
            cursor.subtyping(actual_ty, required_ty);
        }

        for (loc, updated_ty) in fn_sig.ensures {
            let loc = subst.subst_loc(Loc::Abstract(loc));
            let updated_ty = subst.subst_ty(&updated_ty);
            let updated_ty = cursor.unpack(updated_ty);
            if env.has_loc(loc) {
                env.update_loc(cursor, loc, updated_ty);
            } else {
                env.insert_loc(loc, updated_ty);
            }
        }

        if let Some((p, bb)) = destination {
            let ret = subst.subst_ty(&fn_sig.ret);
            let ret = cursor.unpack(ret);
            env.write_place(cursor, p, ret);

            self.check_goto(env, cursor, *bb)?;
        }
        Ok(())
    }

    fn check_assert(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        cond: &Operand,
        expected: bool,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        let cond_ty = self.check_operand(env, cond);

        let pred = match cond_ty.kind() {
            TyKind::Refine(BaseTy::Bool, e) => e.clone(),
            _ => unreachable!("unexpected cond_ty {:?}", cond_ty),
        };

        let assert = if expected { pred } else { pred.not() };

        // Uncomment the below line to allow pre-catching of possible divide-by-zero, underflow, and overflow
        // WARNING: rust is very eager about inserting under/overflow checks, so be warned that uncommenting this will likely break everything
        // cursor.push_head(assert.clone());
        cursor.push_guard(assert);
        self.check_goto(env, cursor, target)?;
        Ok(())
    }

    fn check_switch_int(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        discr: &Operand,
        targets: &mir::SwitchTargets,
    ) -> Result<(), ErrorReported> {
        let discr_ty = self.check_operand(env, discr);
        let mk = |bits| match discr_ty.kind() {
            TyKind::Refine(BaseTy::Bool, e) => {
                if bits != 0 {
                    e.clone()
                } else {
                    e.not()
                }
            }
            TyKind::Refine(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), e) => {
                ExprKind::BinaryOp(BinOp::Eq, e.clone(), Expr::from_bits(bty, bits)).intern()
            }
            _ => unreachable!("unexpected discr_ty {:?}", discr_ty),
        };

        for (bits, bb) in targets.iter() {
            let cursor = &mut cursor.snapshot();
            cursor.push_guard(mk(bits));
            self.check_goto(&mut env.clone(), cursor, bb)?;
        }
        let otherwise = targets
            .iter()
            .map(|(bits, _)| mk(bits).not())
            .reduce(|e1, e2| ExprKind::BinaryOp(BinOp::And, e1, e2).intern());

        let cursor = &mut cursor.snapshot();
        if let Some(otherwise) = otherwise {
            cursor.push_guard(otherwise);
        }

        self.check_goto(env, cursor, targets.otherwise())?;
        Ok(())
    }

    fn check_goto(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        if self.body.is_join_point(target) {
            self.check_goto_join_point(env, cursor, target)
        } else {
            self.check_basic_block(env, cursor, target)
        }
    }

    fn check_goto_join_point(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        match &mut self.mode {
            Mode::Inference(bb_envs) => {
                match bb_envs.entry(target) {
                    Entry::Occupied(mut entry) => {
                        entry.get_mut().join_with(env, cursor);
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(env.clone());
                    }
                };
            }
            Mode::Check {
                shapes, bb_envs, ..
            } => {
                let bb_env = bb_envs
                    .entry(target)
                    .or_insert_with(|| shapes.remove(&target).unwrap().into_bb_env(cursor, env));

                let mut subst = Subst::empty();
                subst
                    .infer_from_bb_env(env, bb_env)
                    .unwrap_or_else(|_| panic!("inference failed"));

                for param in &bb_env.params {
                    cursor.push_head(subst.subst_pred(&param.pred));
                }
                env.transform_into(cursor, &bb_env.subst(self.global_env.tcx, &subst));
            }
        };
        Ok(())
    }

    fn check_rvalue(&self, env: &mut TypeEnv<'tcx>, cursor: &mut Cursor, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(env, cursor, bin_op, op1, op2)
            }
            Rvalue::MutRef(place) => {
                // OWNERSHIP SAFETY CHECK
                TyKind::StrgRef(env.get_loc(place)).intern()
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(env, *un_op, op),
        }
    }

    fn check_binary_op(
        &self,
        env: &mut TypeEnv,
        cursor: &mut Cursor,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.check_operand(env, op1);
        let ty2 = self.check_operand(env, op2);

        match bin_op {
            ir::BinOp::Eq => self.check_eq(BinOp::Eq, ty1, ty2),
            ir::BinOp::Ne => self.check_eq(BinOp::Ne, ty1, ty2),
            ir::BinOp::Add => self.check_arith_op(cursor, BinOp::Add, ty1, ty2),
            ir::BinOp::Sub => self.check_arith_op(cursor, BinOp::Sub, ty1, ty2),
            ir::BinOp::Mul => self.check_arith_op(cursor, BinOp::Mul, ty1, ty2),
            ir::BinOp::Div => self.check_arith_op(cursor, BinOp::Div, ty1, ty2),
            ir::BinOp::Gt => self.check_cmp_op(BinOp::Gt, ty1, ty2),
            ir::BinOp::Lt => self.check_cmp_op(BinOp::Lt, ty1, ty2),
            ir::BinOp::Le => self.check_cmp_op(BinOp::Le, ty1, ty2),
        }
    }

    fn check_arith_op(&self, cursor: &mut Cursor, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        let (bty, e1, e2) = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (BaseTy::Int(*int_ty1), e1.clone(), e2.clone())
            }
            (
                TyKind::Refine(BaseTy::Uint(uint_ty1), e1),
                TyKind::Refine(BaseTy::Uint(uint_ty2), e2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (BaseTy::Uint(*uint_ty1), e1.clone(), e2.clone())
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        if matches!(op, BinOp::Div) {
            cursor.push_head(ExprKind::BinaryOp(BinOp::Ne, e2.clone(), Expr::zero()).intern());
        }
        TyKind::Refine(bty, ExprKind::BinaryOp(op, e1, e2).intern()).intern()
    }

    fn check_cmp_op(&self, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        let (e1, e2) = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                (e1.clone(), e2.clone())
            }
            (
                TyKind::Refine(BaseTy::Uint(uint_ty1), e1),
                TyKind::Refine(BaseTy::Uint(uint_ty2), e2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                (e1.clone(), e2.clone())
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        TyKind::Refine(BaseTy::Bool, ExprKind::BinaryOp(op, e1, e2).intern()).intern()
    }

    fn check_eq(&self, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                TyKind::Refine(
                    BaseTy::Bool,
                    ExprKind::BinaryOp(op, e1.clone(), e2.clone()).intern(),
                )
                .intern()
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_unary_op(&self, env: &mut TypeEnv, un_op: ir::UnOp, op: &Operand) -> Ty {
        let ty = self.check_operand(env, op);
        match un_op {
            ir::UnOp::Not => match ty.kind() {
                TyKind::Refine(BaseTy::Bool, e) => TyKind::Refine(BaseTy::Bool, e.not()).intern(),
                _ => unreachable!("incompatible type: `{:?}`", ty),
            },
            ir::UnOp::Neg => match ty.kind() {
                TyKind::Refine(BaseTy::Int(int_ty), e) => {
                    TyKind::Refine(BaseTy::Int(*int_ty), e.neg()).intern()
                }
                _ => unreachable!("incompatible type: `{:?}`", ty),
            },
        }
    }

    fn check_operand(&self, env: &mut TypeEnv, operand: &Operand) -> Ty {
        match operand {
            Operand::Copy(p) => {
                // OWNERSHIP SAFETY CHECK
                env.lookup_place(p)
            }
            Operand::Move(p) => {
                // OWNERSHIP SAFETY CHECK
                env.move_place(p)
            }
            Operand::Constant(c) => self.check_constant(c),
        }
    }

    fn check_constant(&self, c: &Constant) -> Ty {
        match c {
            Constant::Int(n, int_ty) => {
                let expr = ExprKind::Constant(ty::Constant::from(*n)).intern();
                TyKind::Refine(BaseTy::Int(*int_ty), expr).intern()
            }
            Constant::Uint(n, uint_ty) => {
                let expr = ExprKind::Constant(ty::Constant::from(*n)).intern();
                TyKind::Refine(BaseTy::Uint(*uint_ty), expr).intern()
            }
            Constant::Bool(b) => {
                let expr = ExprKind::Constant(ty::Constant::from(*b)).intern();
                TyKind::Refine(BaseTy::Bool, expr).intern()
            }
        }
    }

    fn report_inference_error(&self, call_source_info: SourceInfo) -> Result<(), ErrorReported> {
        self.sess
            .span_err(call_source_info.span, "inference error at function call");
        Err(ErrorReported)
    }
}
