extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{hash_map::Entry, BinaryHeap};

use crate::{
    global_env::GlobalEnv,
    lowering::LoweringCtxt,
    pure_ctxt::{Cursor, KVarStore, PureCtxt, Scope, Snapshot},
    subst::Subst,
    subtyping::{Sub, Tag},
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
use rustc_middle::mir;
use rustc_session::Session;

use super::type_env::TypeEnvShape;

pub struct Checker<'a, 'tcx, M> {
    sess: &'a Session,
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    genv: &'a GlobalEnv<'tcx>,
    mode: M,
    ret: Ty,
    ensures: Vec<(Name, Ty)>,
    /// A snapshot of the pure context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: &'a Dominators<BasicBlock>,
    queue: WorkQueue<'a>,
}

pub trait Mode {
    fn fresh_kvar<I>(&mut self, sort: Sort, scope: I) -> Pred
    where
        I: IntoIterator<Item = (Name, Sort)>;

    fn enter_basic_block(&mut self, cursor: &mut Cursor, bb: BasicBlock) -> TypeEnv;

    fn check_goto_join_point(
        &mut self,
        genv: &GlobalEnv,
        cursor: Cursor,
        env: TypeEnv,
        scope: &Scope,
        target: BasicBlock,
    ) -> bool;

    fn clear(&mut self, bb: BasicBlock);
}

pub struct Inference<'a> {
    bb_envs: &'a mut FxHashMap<BasicBlock, TypeEnv>,
}

pub struct Check<'a> {
    shapes: FxHashMap<BasicBlock, TypeEnvShape>,
    bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
    kvars: &'a mut KVarStore,
}

impl<'a, 'tcx, M> Checker<'a, 'tcx, M> {
    fn new(
        genv: &'a GlobalEnv<'tcx>,
        body: &'a Body<'tcx>,
        ret: Ty,
        ensures: Vec<(Name, Ty)>,
        dominators: &'a Dominators<BasicBlock>,
        mode: M,
    ) -> Self {
        Checker {
            sess: genv.tcx.sess,
            genv,
            body,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            ret,
            ensures,
            mode,
            snapshots: IndexVec::from_fn_n(|_| None, body.basic_blocks.len()),
            dominators,
            queue: WorkQueue::with_none(body.basic_blocks.len(), dominators),
        }
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Inference<'_>> {
    pub fn infer(
        genv: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvShape>, ErrorReported> {
        let mut pure_cx = PureCtxt::new();
        let fn_sig = LoweringCtxt::lower_fn_sig(genv, fn_sig);

        let mut bb_envs = FxHashMap::default();
        let _ =
            Checker::run(genv, &mut pure_cx, body, &fn_sig, Inference { bb_envs: &mut bb_envs })?;

        Ok(bb_envs
            .into_iter()
            .map(|(bb, env)| (bb, env.into_shape()))
            .collect())
    }
}

impl<'a, 'tcx> Checker<'a, 'tcx, Check<'_>> {
    pub fn check(
        genv: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &core::FnSig,
        shapes: FxHashMap<BasicBlock, TypeEnvShape>,
    ) -> Result<(PureCtxt, KVarStore), ErrorReported> {
        let mut pure_cx = PureCtxt::new();
        let fn_sig = LoweringCtxt::lower_fn_sig(genv, fn_sig);
        let mut kvars = KVarStore::new();

        Checker::run(
            genv,
            &mut pure_cx,
            body,
            &fn_sig,
            Check { shapes, bb_envs: FxHashMap::default(), kvars: &mut kvars },
        )?;

        Ok((pure_cx, kvars))
    }
}

impl<'a, 'tcx, M: Mode> Checker<'a, 'tcx, M> {
    fn run(
        genv: &GlobalEnv<'tcx>,
        pure_cx: &mut PureCtxt,
        body: &Body<'tcx>,
        fn_sig: &FnSig,
        mode: M,
    ) -> Result<(), ErrorReported> {
        let mut cursor = pure_cx.cursor_at_root();
        let mut env = TypeEnv::new();
        let mut subst = Subst::empty();

        for param in &fn_sig.params {
            cursor.push_binding(param.sort.clone(), |fresh| {
                subst.insert_expr(Var::Free(param.name), Var::Free(fresh));
                subst.subst_pred(&param.pred)
            });
        }

        for (loc, ty) in &fn_sig.requires {
            let fresh = cursor.push_loc();
            let ty = env.unpack(genv, &mut cursor, subst.subst_ty(ty));
            env.insert_loc(fresh, ty);
            subst.insert_loc(Loc::Abstract(*loc), fresh);
        }

        for (local, ty) in body.args_iter().zip(&fn_sig.args) {
            let ty = env.unpack(genv, &mut cursor, subst.subst_ty(ty));
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

        let dominators = body.dominators();
        let mut checker = Checker::new(genv, body, ret, ensures, &dominators, mode);

        checker.check_goto(cursor, env, START_BLOCK)?;
        while let Some(bb) = checker.queue.pop() {
            let snapshot = checker.snapshot_at_dominator(bb);
            let mut cursor = pure_cx.cursor_at(snapshot).unwrap();

            if checker.visited.contains(bb) {
                cursor.clear();
                checker.clear(bb);
            }

            let mut env = checker.mode.enter_basic_block(&mut cursor, bb);
            env.unpack_all(genv, &mut cursor);
            checker.check_basic_block(cursor, env, bb)?;
        }

        Ok(())
    }

    fn clear(&mut self, root: BasicBlock) {
        // FIXME: there should be a better way to iterate over all dominated blocks.
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
        mut cursor: Cursor,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        self.visited.insert(bb);

        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(&mut cursor, &mut env, stmt);
        }
        if let Some(terminator) = &data.terminator {
            let successors = self.check_terminator(&mut cursor, &mut env, terminator)?;
            self.snapshots[bb] = Some(cursor.snapshot());
            self.check_successors(cursor, env, successors)?;
        }
        Ok(())
    }

    fn check_statement(&self, cursor: &mut Cursor, env: &mut TypeEnv, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(p, rvalue) => {
                let ty = self.check_rvalue(cursor, env, stmt.source_info, rvalue);
                let ty = env.unpack(self.genv, cursor, ty);
                let sub = &mut Sub::new(
                    self.genv,
                    cursor.breadcrumb(),
                    Tag::Assign(stmt.source_info.span),
                );
                env.write_place(sub, p, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(
        &mut self,
        cursor: &mut Cursor,
        env: &mut TypeEnv,
        terminator: &Terminator,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = env.lookup_local(RETURN_PLACE);
                let sub = &mut Sub::new(self.genv, cursor.breadcrumb(), Tag::Ret);

                sub.subtyping(ret_place_ty, self.ret.clone());

                for (loc, ensured_ty) in &self.ensures {
                    let actual_ty = env.lookup_loc(Loc::Abstract(*loc));
                    sub.subtyping(actual_ty, ensured_ty.clone());
                }
                Ok(vec![])
            }
            TerminatorKind::Goto { target } => Ok(vec![(*target, None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                self.check_switch_int(env, discr, targets)
            }
            TerminatorKind::Call { func, substs, args, destination } => {
                self.check_call(
                    cursor,
                    env,
                    terminator.source_info,
                    *func,
                    substs,
                    args,
                    destination,
                )
            }
            TerminatorKind::Assert { cond, expected, target } => {
                self.check_assert(env, cond, *expected, *target)
            }
            TerminatorKind::Drop { place, target } => {
                let _ = env.move_place(place);
                Ok(vec![(*target, None)])
            }
        }
    }

    fn check_call(
        &mut self,
        cursor: &mut Cursor,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        func: DefId,
        substs: &[core::Ty],
        args: &[Operand],
        destination: &Option<(Place, BasicBlock)>,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        let fn_sig = self.genv.lookup_fn_sig(func);
        let fn_sig = LoweringCtxt::lower_fn_sig(self.genv, fn_sig);

        let actuals = args
            .iter()
            .map(|arg| self.check_operand(env, arg))
            .collect_vec();

        let cx = LoweringCtxt::empty(self.genv);
        let scope = cursor.scope();
        let fresh_kvar = &mut |sort| self.mode.fresh_kvar(sort, scope.iter());
        let substs = substs
            .iter()
            .map(|ty| cx.lower_ty(ty, fresh_kvar))
            .collect();

        let mut subst = Subst::with_type_substs(substs);
        if subst.infer_from_fn_call(env, &actuals, &fn_sig).is_err() {
            self.sess
                .emit_err(errors::ParamInferenceError { span: source_info.span });
            return Err(ErrorReported);
        };

        for param in fn_sig.params {
            cursor.push_head(subst.subst_pred(&param.pred), Tag::Call(source_info.span));
        }

        let sub = &mut Sub::new(self.genv, cursor.breadcrumb(), Tag::Call(source_info.span));
        for (actual, formal) in actuals.into_iter().zip(&fn_sig.args) {
            sub.subtyping(actual, subst.subst_ty(formal));
        }

        for (loc, required_ty) in fn_sig.requires {
            let loc = subst.subst_loc(Loc::Abstract(loc));
            let actual_ty = env.lookup_loc(loc);
            let required_ty = subst.subst_ty(&required_ty);
            sub.subtyping(actual_ty, required_ty);
        }

        for (loc, updated_ty) in fn_sig.ensures {
            let loc = Loc::Abstract(loc);
            let updated_ty = subst.subst_ty(&updated_ty);
            let updated_ty = env.unpack(self.genv, cursor, updated_ty);
            if subst.has_loc(loc) {
                let loc = subst.subst_loc(loc);
                let sub =
                    &mut Sub::new(self.genv, cursor.breadcrumb(), Tag::Call(source_info.span));
                env.update_loc(sub, loc, updated_ty);
            } else {
                let fresh = cursor.push_loc();
                subst.insert_loc(loc, fresh);
                env.insert_loc(fresh, updated_ty);
            }
        }

        let mut successors = vec![];
        if let Some((p, bb)) = destination {
            let ret = subst.subst_ty(&fn_sig.ret);
            let ret = env.unpack(self.genv, cursor, ret);
            let sub = &mut Sub::new(self.genv, cursor.breadcrumb(), Tag::Call(source_info.span));
            env.write_place(sub, p, ret);
            successors.push((*bb, None));
        }
        Ok(successors)
    }

    fn check_assert(
        &mut self,
        env: &mut TypeEnv,
        cond: &Operand,
        expected: bool,
        target: BasicBlock,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        let cond_ty = self.check_operand(env, cond);

        let pred = match cond_ty.kind() {
            TyKind::Refine(BaseTy::Bool, e) => e.clone(),
            _ => unreachable!("unexpected cond_ty {:?}", cond_ty),
        };

        let assert = if expected { pred } else { pred.not() };

        Ok(vec![(target, Some(assert))])
    }

    fn check_switch_int(
        &mut self,
        env: &mut TypeEnv,
        discr: &Operand,
        targets: &mir::SwitchTargets,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        let discr_ty = self.check_operand(env, discr);
        let mk = |bits| {
            match discr_ty.kind() {
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
            }
        };

        let mut successors = vec![];

        for (bits, bb) in targets.iter() {
            successors.push((bb, Some(mk(bits))));
        }
        let otherwise = targets
            .iter()
            .map(|(bits, _)| mk(bits).not())
            .reduce(|e1, e2| ExprKind::BinaryOp(BinOp::And, e1, e2).intern());

        successors.push((targets.otherwise(), otherwise));

        Ok(successors)
    }

    fn check_successors(
        &mut self,
        mut cursor: Cursor,
        env: TypeEnv,
        successors: Vec<(BasicBlock, Option<Expr>)>,
    ) -> Result<(), ErrorReported> {
        for (target, guard) in successors {
            let mut cursor = cursor.breadcrumb();
            let env = env.clone();
            if let Some(guard) = guard {
                cursor.push_pred(guard);
            }
            self.check_goto(cursor, env, target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        cursor: Cursor,
        env: TypeEnv,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        if self.body.is_join_point(target) {
            let scope = cursor.scope_at(self.snapshot_at_dominator(target)).unwrap();
            if self
                .mode
                .check_goto_join_point(self.genv, cursor, env, &scope, target)
            {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.check_basic_block(cursor, env, target)
        }
    }

    fn check_rvalue(
        &self,
        cursor: &mut Cursor,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        rvalue: &Rvalue,
    ) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(cursor, env, source_info, bin_op, op1, op2)
            }
            Rvalue::MutRef(place) => {
                // OWNERSHIP SAFETY CHECK
                env.borrow_mut(place)
            }
            Rvalue::ShrRef(place) => {
                // OWNERSHIP SAFETY CHECK
                env.borrow_shr(place)
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(env, *un_op, op),
        }
    }

    fn check_binary_op(
        &self,
        cursor: &mut Cursor,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.check_operand(env, op1);
        let ty2 = self.check_operand(env, op2);

        match bin_op {
            ir::BinOp::Eq => self.check_eq(BinOp::Eq, ty1, ty2),
            ir::BinOp::Ne => self.check_eq(BinOp::Ne, ty1, ty2),
            ir::BinOp::Add => self.check_arith_op(cursor, source_info, BinOp::Add, ty1, ty2),
            ir::BinOp::Sub => self.check_arith_op(cursor, source_info, BinOp::Sub, ty1, ty2),
            ir::BinOp::Mul => self.check_arith_op(cursor, source_info, BinOp::Mul, ty1, ty2),
            ir::BinOp::Div => self.check_arith_op(cursor, source_info, BinOp::Div, ty1, ty2),
            ir::BinOp::Rem => self.check_rem(cursor, source_info, ty1, ty2),
            ir::BinOp::Gt => self.check_cmp_op(BinOp::Gt, ty1, ty2),
            ir::BinOp::Ge => self.check_cmp_op(BinOp::Ge, ty1, ty2),
            ir::BinOp::Lt => self.check_cmp_op(BinOp::Lt, ty1, ty2),
            ir::BinOp::Le => self.check_cmp_op(BinOp::Le, ty1, ty2),
            ir::BinOp::BitAnd => self.check_bitwise_op(BinOp::And, ty1, ty2),
        }
    }

    fn check_bitwise_op(&self, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), _e1),
                TyKind::Refine(BaseTy::Int(int_ty2), _e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                TyKind::Exists(BaseTy::Int(*int_ty1), Expr::tt().into()).intern()
            }
            (
                TyKind::Refine(BaseTy::Uint(uint_ty1), _e1),
                TyKind::Refine(BaseTy::Uint(uint_ty2), _e2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                TyKind::Refine(
                    BaseTy::Uint(*uint_ty1),
                    ExprKind::Constant(liquid_rust_fixpoint::Constant::Bool(true)).intern(),
                )
                .intern()
            }
            (TyKind::Refine(BaseTy::Bool, e1), TyKind::Refine(BaseTy::Bool, e2)) => {
                TyKind::Refine(
                    BaseTy::Bool,
                    ExprKind::BinaryOp(op, e1.clone(), e2.clone()).intern(),
                )
                .intern()
            }
            _ => unreachable!("non-boolean arguments to bitwise op: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    // Rem is a special case due to differing semantics with negative numbers
    fn check_rem(&self, cursor: &mut Cursor, source_info: SourceInfo, ty1: Ty, ty2: Ty) -> Ty {
        let ty = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                cursor.push_head(
                    ExprKind::BinaryOp(BinOp::Ne, e2.clone(), Expr::zero()).intern(),
                    Tag::Rem(source_info.span),
                );

                let bty = BaseTy::Int(*int_ty1);
                let binding = ExprKind::BinaryOp(
                    BinOp::Eq,
                    ExprKind::Var(Var::Bound).intern(),
                    ExprKind::BinaryOp(BinOp::Mod, e1.clone(), e2.clone()).intern(),
                )
                .intern();
                let guard = ExprKind::BinaryOp(
                    BinOp::And,
                    ExprKind::BinaryOp(BinOp::Ge, e1.clone(), Expr::zero()).intern(),
                    ExprKind::BinaryOp(BinOp::Ge, e2.clone(), Expr::zero()).intern(),
                )
                .intern();
                let pred = ty::Pred::Expr(ExprKind::BinaryOp(BinOp::Imp, guard, binding).intern());

                TyKind::Exists(bty, pred).intern()
            }
            (
                TyKind::Refine(BaseTy::Uint(uint_ty1), e1),
                TyKind::Refine(BaseTy::Uint(uint_ty2), e2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                cursor.push_head(
                    ExprKind::BinaryOp(BinOp::Ne, e2.clone(), Expr::zero()).intern(),
                    Tag::Rem(source_info.span),
                );

                TyKind::Refine(
                    BaseTy::Uint(*uint_ty1),
                    ExprKind::BinaryOp(BinOp::Mod, e1.clone(), e2.clone()).intern(),
                )
                .intern()
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };

        ty
    }

    fn check_arith_op(
        &self,
        cursor: &mut Cursor,
        source_info: SourceInfo,
        op: BinOp,
        ty1: Ty,
        ty2: Ty,
    ) -> Ty {
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
            cursor.push_head(
                ExprKind::BinaryOp(BinOp::Ne, e2.clone(), Expr::zero()).intern(),
                Tag::Div(source_info.span),
            );
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
            ir::UnOp::Not => {
                match ty.kind() {
                    TyKind::Refine(BaseTy::Bool, e) => {
                        TyKind::Refine(BaseTy::Bool, e.not()).intern()
                    }
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
            ir::UnOp::Neg => {
                match ty.kind() {
                    TyKind::Refine(BaseTy::Int(int_ty), e) => {
                        TyKind::Refine(BaseTy::Int(*int_ty), e.neg()).intern()
                    }
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
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

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
    }
}

impl Mode for Inference<'_> {
    fn enter_basic_block(&mut self, _cursor: &mut Cursor, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].clone()
    }

    fn check_goto_join_point(
        &mut self,
        genv: &GlobalEnv,
        _cursor: Cursor,
        mut env: TypeEnv,
        scope: &Scope,
        target: BasicBlock,
    ) -> bool {
        env.pack_refs(scope);
        match self.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(genv, &mut env),
            Entry::Vacant(entry) => {
                entry.insert(env.clone());
                true
            }
        }
    }

    fn fresh_kvar<I>(&mut self, _sort: Sort, _scope: I) -> Pred
    where
        I: IntoIterator<Item = (Name, Sort)>,
    {
        Pred::dummy_kvar()
    }

    fn clear(&mut self, bb: BasicBlock) {
        self.bb_envs.remove(&bb);
    }
}

impl Mode for Check<'_> {
    fn enter_basic_block(&mut self, cursor: &mut Cursor, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter(cursor)
    }

    fn check_goto_join_point(
        &mut self,
        genv: &GlobalEnv,
        mut cursor: Cursor,
        mut env: TypeEnv,
        scope: &Scope,
        target: BasicBlock,
    ) -> bool {
        env.pack_refs(scope);
        let fresh_kvar = &mut |var, sort, params: &[Param]| {
            self.kvars.fresh(
                var,
                sort,
                scope
                    .iter()
                    .chain(params.iter().map(|param| (param.name, param.sort.clone()))),
            )
        };
        let mut first = false;
        let bb_env = self.bb_envs.entry(target).or_insert_with(|| {
            first = true;
            self.shapes.remove(&target).unwrap().into_bb_env(
                genv,
                &cursor.name_gen(),
                fresh_kvar,
                &env,
            )
        });

        let mut subst = Subst::empty();
        subst
            .infer_from_bb_env(&env, bb_env)
            .unwrap_or_else(|_| panic!("inference failed"));

        for param in &bb_env.params {
            cursor.push_head(subst.subst_pred(&param.pred), Tag::Goto);
        }
        let sub = &mut Sub::new(genv, cursor.breadcrumb(), Tag::Goto);
        env.transform_into(sub, &bb_env.subst(&subst));

        first
    }

    fn fresh_kvar<I>(&mut self, sort: Sort, scope: I) -> Pred
    where
        I: IntoIterator<Item = (Name, Sort)>,
    {
        self.kvars.fresh(Var::Bound, sort, scope)
    }

    fn clear(&mut self, _bb: BasicBlock) {
        unreachable!()
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
    fn with_none(len: usize, dominators: &'a Dominators<BasicBlock>) -> Self {
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
