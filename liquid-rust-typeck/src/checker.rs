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
    global_env::GlobalEnv,
    lowering::LoweringCtxt,
    pure_ctxt::{Cursor, KVarStore, PureCtxt, Snapshot},
    subst::Subst,
    ty::{
        self, BaseTy, BinOp, Expr, ExprKind, FnSig, Loc, Name, Param, Pred, Sort, Ty, TyKind, Var,
    },
    type_env::{BasicBlockEnv, TypeEnv},
};
use itertools::Itertools;
use liquid_rust_common::{errors::ErrorReported, index::IndexVec};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Operand, Place, Rvalue, SourceInfo, Statement,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
    },
    ty as core,
};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_session::Session;

use super::type_env::TypeEnvShape;

pub struct Checker<'a, 'tcx, M> {
    sess: &'a Session,
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    global_env: &'a GlobalEnv<'tcx>,
    mode: M,
    ret: Ty,
    kvars: KVarStore,
    ensures: Vec<(Name, Ty)>,
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: Dominators<BasicBlock>,
}

pub trait Mode<'tcx> {
    fn enter_basic_block(
        &mut self,
        tcx: TyCtxt<'tcx>,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> TypeEnv<'tcx>;

    fn check_goto_join_point(
        &mut self,
        tcx: TyCtxt<'tcx>,
        cursor: &mut Cursor,
        env: &mut TypeEnv<'tcx>,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        target: BasicBlock,
    );
}

pub struct Inference<'a, 'tcx> {
    bb_envs: &'a mut FxHashMap<BasicBlock, TypeEnv<'tcx>>,
}

pub struct Check {
    shapes: FxHashMap<BasicBlock, TypeEnvShape>,
    bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
}

impl<'a, 'tcx, M> Checker<'a, 'tcx, M> {
    fn new(
        global_env: &'a GlobalEnv<'tcx>,
        body: &'a Body<'tcx>,
        ret: Ty,
        ensures: Vec<(Name, Ty)>,
        mode: M,
    ) -> Self {
        Checker {
            sess: global_env.tcx.sess,
            global_env,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            ret,
            ensures,
            mode,
            kvars: KVarStore::new(),
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            dominators: body.dominators(),
        }
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Inference<'_, 'tcx>> {
    pub fn infer(
        global_env: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvShape>, ErrorReported> {
        let mut pure_cx = PureCtxt::new();
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig);

        let mut bb_envs = FxHashMap::default();
        let _ = Checker::run(
            global_env,
            &mut pure_cx,
            body,
            &fn_sig,
            Inference {
                bb_envs: &mut bb_envs,
            },
        )?;

        Ok(bb_envs
            .into_iter()
            .map(|(bb, env)| (bb, env.into_shape()))
            .collect())
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Check> {
    pub fn check(
        global_env: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
        shapes: FxHashMap<BasicBlock, TypeEnvShape>,
    ) -> Result<(PureCtxt, KVarStore), ErrorReported> {
        let mut pure_cx = PureCtxt::new();
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig);

        let kvars = Checker::run(
            global_env,
            &mut pure_cx,
            body,
            &fn_sig,
            Check {
                shapes,
                bb_envs: FxHashMap::default(),
            },
        )?;
        Ok((pure_cx, kvars))
    }
}

impl<'a, 'tcx, M: Mode<'tcx>> Checker<'a, 'tcx, M> {
    fn run(
        global_env: &GlobalEnv<'tcx>,
        pure_cx: &mut PureCtxt,
        body: &Body<'tcx>,
        fn_sig: &FnSig,
        mode: M,
    ) -> Result<KVarStore, ErrorReported> {
        let cursor = &mut pure_cx.cursor_at_root();
        let mut env = TypeEnv::new(global_env.tcx);
        let mut subst = Subst::empty();

        for param in &fn_sig.params {
            cursor.push_binding(param.sort, |fresh| {
                subst.insert_expr(Var::Free(param.name), Var::Free(fresh));
                subst.subst_pred(&param.pred)
            });
        }

        for (loc, ty) in &fn_sig.requires {
            let fresh = cursor.push_loc();
            let ty = env.unpack(cursor, subst.subst_ty(ty));
            env.insert_loc(fresh, ty);
            subst.insert_loc(Loc::Abstract(*loc), fresh);
        }

        for (local, ty) in body.args_iter().zip(&fn_sig.args) {
            let ty = env.unpack(cursor, subst.subst_ty(ty));
            env.insert_loc(Loc::Local(local), ty);
        }

        for local in body.vars_and_temps_iter() {
            env.insert_loc(Loc::Local(local), TyKind::Uninit.intern())
        }

        env.insert_loc(Loc::Local(RETURN_PLACE), TyKind::Uninit.intern());

        let ret = subst.subst_ty(&fn_sig.ret);
        let ensures = fn_sig
            .ensures
            .iter()
            .map(|(loc, ty)| (*loc, subst.subst_ty(ty)))
            .collect();

        let mut checker = Checker::new(global_env, body, ret, ensures, mode);

        checker.check_goto(&mut env, cursor, START_BLOCK)?;
        for bb in body.reverse_postorder() {
            if !checker.visited.contains(bb) {
                let mut env = checker
                    .mode
                    .enter_basic_block(checker.global_env.tcx, cursor, bb);
                env.unpack_all(cursor);
                checker.check_basic_block(&mut env, cursor, bb)?;
            }
        }

        Ok(checker.kvars)
    }

    fn check_basic_block(
        &mut self,
        env: &mut TypeEnv<'tcx>,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        self.visited.insert(bb);

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
                let ty = env.unpack(cursor, ty);
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
                cursor.subtyping(self.global_env.tcx, ret_place_ty, self.ret.clone());

                for (loc, ensured_ty) in &self.ensures {
                    let actual_ty = env.lookup_loc(Loc::Abstract(*loc)).unwrap();
                    cursor.subtyping(self.global_env.tcx, actual_ty, ensured_ty.clone());
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
        let fn_sig = LoweringCtxt::lower_fn_sig(fn_sig);

        let actuals = args
            .iter()
            .map(|arg| self.check_operand(env, arg))
            .collect_vec();

        let cx = LoweringCtxt::empty();
        let scope = cursor.scope();
        let fresh_kvar = &mut |sort| self.kvars.fresh(Var::Bound, sort, scope.iter().copied());
        let substs = substs
            .iter()
            .map(|ty| cx.lower_ty(ty, fresh_kvar))
            .collect();

        let mut subst = Subst::with_type_substs(substs);
        if subst.infer_from_fn_call(env, &actuals, &fn_sig).is_err() {
            return self.report_inference_error(source_info);
        };

        for param in fn_sig.params {
            cursor.push_head(subst.subst_pred(&param.pred));
        }

        for (actual, formal) in actuals.into_iter().zip(&fn_sig.args) {
            cursor.subtyping(self.global_env.tcx, actual, subst.subst_ty(formal));
        }

        for (loc, required_ty) in fn_sig.requires {
            let loc = subst.subst_loc(Loc::Abstract(loc));
            let actual_ty = env.lookup_loc(loc).unwrap();
            let required_ty = subst.subst_ty(&required_ty);
            cursor.subtyping(self.global_env.tcx, actual_ty, required_ty);
        }

        for (loc, updated_ty) in fn_sig.ensures {
            let loc = subst.subst_loc(Loc::Abstract(loc));
            let updated_ty = subst.subst_ty(&updated_ty);
            let updated_ty = env.unpack(cursor, updated_ty);
            if env.has_loc(loc) {
                env.update_loc(cursor, loc, updated_ty);
            } else {
                let fresh = cursor.push_loc();
                subst.insert_loc(loc, fresh);
                env.insert_loc(fresh, updated_ty);
            }
        }

        if let Some((p, bb)) = destination {
            let ret = subst.subst_ty(&fn_sig.ret);
            let ret = env.unpack(cursor, ret);
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
        cursor.push_pred(assert);
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
            let cursor = &mut cursor.breadcrumb();
            cursor.push_pred(mk(bits));
            self.check_goto(&mut env.clone(), cursor, bb)?;
        }
        let otherwise = targets
            .iter()
            .map(|(bits, _)| mk(bits).not())
            .reduce(|e1, e2| ExprKind::BinaryOp(BinOp::And, e1, e2).intern());

        let cursor = &mut cursor.breadcrumb();
        if let Some(otherwise) = otherwise {
            cursor.push_pred(otherwise);
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
        self.snapshots[target] = Some(cursor.snapshot());

        if self.body.is_join_point(target) {
            let dominator = self.dominators.immediate_dominator(target);
            let scope = cursor
                .scope_at(self.snapshots[dominator].as_ref().unwrap())
                .unwrap();
            let fresh_kvar = &mut |var, sort, params: &[Param]| {
                self.kvars.fresh(
                    var,
                    sort,
                    scope.iter().copied().chain(
                        params
                            .iter()
                            .map(|param| (Var::Free(param.name), param.sort)),
                    ),
                )
            };
            self.mode
                .check_goto_join_point(self.global_env.tcx, cursor, env, fresh_kvar, target);
            Ok(())
        } else {
            self.check_basic_block(env, cursor, target)
        }
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

impl<'tcx> Mode<'tcx> for Inference<'_, 'tcx> {
    fn enter_basic_block(
        &mut self,
        _tcx: TyCtxt<'tcx>,
        _cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> TypeEnv<'tcx> {
        self.bb_envs[&bb].clone()
    }

    fn check_goto_join_point(
        &mut self,
        _tcx: TyCtxt<'tcx>,
        cursor: &mut Cursor,
        env: &mut TypeEnv<'tcx>,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        target: BasicBlock,
    ) {
        match self.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => {
                entry
                    .get_mut()
                    .join_with(env, cursor, &mut |sort| fresh_kvar(Var::Bound, sort, &[]));
            }
            Entry::Vacant(entry) => {
                entry.insert(env.clone());
            }
        }
    }
}

impl<'tcx> Mode<'tcx> for Check {
    fn enter_basic_block(
        &mut self,
        tcx: TyCtxt<'tcx>,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> TypeEnv<'tcx> {
        self.bb_envs[&bb].enter(tcx, cursor)
    }

    fn check_goto_join_point(
        &mut self,
        tcx: TyCtxt<'tcx>,
        cursor: &mut Cursor,
        env: &mut TypeEnv<'tcx>,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        target: BasicBlock,
    ) {
        let bb_env = self.bb_envs.entry(target).or_insert_with(|| {
            self.shapes
                .remove(&target)
                .unwrap()
                .into_bb_env(&cursor.name_gen(), fresh_kvar, env)
        });

        let mut subst = Subst::empty();
        subst
            .infer_from_bb_env(env, bb_env)
            .unwrap_or_else(|_| panic!("inference failed"));

        for param in &bb_env.params {
            cursor.push_head(subst.subst_pred(&param.pred));
        }
        env.transform_into(cursor, &bb_env.subst(tcx, &subst));
    }
}
