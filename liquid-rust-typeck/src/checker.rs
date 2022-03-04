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
    constraint_gen::{ConstraintGen, Tag},
    dbg,
    global_env::GlobalEnv,
    lowering::LoweringCtxt,
    pure_ctxt::{ConstraintBuilder, KVarStore, PureCtxt, Snapshot},
    subst::Subst,
    ty::{self, BaseTy, BinOp, Constr, Expr, FnSig, Name, Param, Pred, Sort, Ty, TyKind, Var},
    type_env::{BasicBlockEnv, TypeEnv, TypeEnvInfer},
};
use itertools::Itertools;
use liquid_rust_common::{errors::ErrorReported, index::IndexVec};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Operand, Place, Rvalue, SourceInfo, Statement,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
    },
    ty::{self as core, Layout},
};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir;
use rustc_session::Session;

pub struct Checker<'a, 'tcx, M> {
    sess: &'a Session,
    body: &'a Body<'tcx>,
    visited: BitSet<BasicBlock>,
    genv: &'a GlobalEnv<'tcx>,
    mode: M,
    ret: Ty,
    ensures: Vec<Constr>,
    /// A snapshot of the pure context at the end of the basic block after applying the effects
    /// of the terminator.
    snapshots: IndexVec<BasicBlock, Option<Snapshot>>,
    dominators: &'a Dominators<BasicBlock>,
    queue: WorkQueue<'a>,
}

pub trait Mode: Sized {
    fn fresh_kvar<I>(&mut self, sort: Sort, scope: I) -> Pred
    where
        I: IntoIterator<Item = (Name, Sort)>;

    fn enter_basic_block(&mut self, pcx: &mut PureCtxt, bb: BasicBlock) -> TypeEnv;

    fn check_goto_join_point(
        ck: &mut Checker<Self>,
        pcx: PureCtxt,
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

impl<'a, 'tcx, M> Checker<'a, 'tcx, M> {
    fn new(
        genv: &'a GlobalEnv<'tcx>,
        body: &'a Body<'tcx>,
        ret: Ty,
        ensures: Vec<Constr>,
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
        def_id: DefId,
    ) -> Result<FxHashMap<BasicBlock, TypeEnvInfer>, ErrorReported> {
        dbg::infer_span!(genv.tcx, def_id).in_scope(|| {
            let mut constraint = ConstraintBuilder::new();

            let mut bb_envs = FxHashMap::default();
            Checker::run(genv, &mut constraint, body, def_id, Inference { bb_envs: &mut bb_envs })?;

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
    ) -> Result<ConstraintBuilder, ErrorReported> {
        dbg::check_span!(genv.tcx, def_id, bb_envs_infer).in_scope(|| {
            let mut constraint = ConstraintBuilder::new();

            Checker::run(
                genv,
                &mut constraint,
                body,
                def_id,
                Check { bb_envs_infer, bb_envs: FxHashMap::default(), kvars },
            )?;

            Ok(constraint)
        })
    }
}

impl<'a, 'tcx, M: Mode> Checker<'a, 'tcx, M> {
    fn run(
        genv: &'a GlobalEnv<'tcx>,
        constraint: &mut ConstraintBuilder,
        body: &'a Body<'tcx>,
        def_id: DefId,
        mode: M,
    ) -> Result<(), ErrorReported> {
        let fn_sig = genv.lookup_fn_sig(def_id);

        let mut pcx = constraint.pure_context_at_root();
        let subst = Subst::with_fresh_names(&mut pcx, &fn_sig.params);

        let fn_sig = subst.subst_fn_sig(&fn_sig.value);

        let env = Self::init(genv, &mut pcx, body, &fn_sig);

        let dominators = body.dominators();
        let mut ck = Checker::new(genv, body, fn_sig.ret, fn_sig.ensures, &dominators, mode);

        ck.check_goto(pcx, env, None, START_BLOCK)?;
        while let Some(bb) = ck.queue.pop() {
            let snapshot = ck.snapshot_at_dominator(bb);
            let mut pcx = constraint.pure_context_at(snapshot).unwrap();

            if ck.visited.contains(bb) {
                pcx.clear();
                ck.clear(bb);
            }

            let mut env = ck.mode.enter_basic_block(&mut pcx, bb);
            env.unpack(genv, &mut pcx);
            ck.check_basic_block(pcx, env, bb)?;
        }

        Ok(())
    }

    fn init(genv: &GlobalEnv, pcx: &mut PureCtxt, body: &Body, fn_sig: &FnSig) -> TypeEnv {
        let mut env = TypeEnv::new();
        for constr in &fn_sig.requires {
            match constr {
                ty::Constr::Type(loc, ty) => {
                    let ty = env.unpack_ty(genv, pcx, ty);
                    env.alloc_with_ty(*loc, ty);
                }
                ty::Constr::Pred(e) => {
                    pcx.push_pred(e.clone());
                }
            }
        }

        for (local, ty) in body.args_iter().zip(&fn_sig.args) {
            let ty = env.unpack_ty(genv, pcx, ty);
            env.alloc_with_ty(local, ty);
        }

        for local in body.vars_and_temps_iter() {
            env.alloc(local, body.local_decls[local].layout);
        }

        env.alloc(RETURN_PLACE, body.local_decls[RETURN_PLACE].layout);
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
        mut pcx: PureCtxt,
        mut env: TypeEnv,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        dbg::basic_block_start!(bb, pcx, env);

        self.visited.insert(bb);

        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(&mut pcx, &mut env, stmt);

            dbg::statement_end!(stmt, pcx, env);
        }
        if let Some(terminator) = &data.terminator {
            let successors = self.check_terminator(&mut pcx, &mut env, terminator)?;
            dbg::terminator_end!(terminator, pcx, env);

            self.snapshots[bb] = Some(pcx.snapshot());
            self.check_successors(pcx, env, terminator.source_info, successors)?;
        }
        Ok(())
    }

    fn check_statement(&self, pcx: &mut PureCtxt, env: &mut TypeEnv, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(p, rvalue) => {
                let ty = self.check_rvalue(pcx, env, stmt.source_info, rvalue);
                let ty = env.unpack_ty(self.genv, pcx, &ty);
                let gen = &mut ConstraintGen::new(
                    self.genv,
                    pcx.breadcrumb(),
                    Tag::Assign(stmt.source_info.span),
                );
                env.write_place(gen, p, ty);
            }
            StatementKind::Nop => {}
            StatementKind::Fold(place) => {
                let layout = env.layout(place);
                if let Layout::Adt(did) = layout {
                    let adt_def = self.genv.adt_def(did);
                    // let e = adt_def.fol
                    todo!()
                } else {
                    panic!("layout cannot be folded: `{layout:?}`")
                }
            }
            StatementKind::Unfold(place) => {
                let ty = env.lookup_place(place);
                if let TyKind::Refine(BaseTy::Adt(did, substs), e) = ty.kind() {
                    let adt_def = self.genv.adt_def(*did);
                    let fields = adt_def.unfold(substs, e);
                    env.unfold(place, fields);
                } else {
                    panic!("type cannot be unfolded: `{ty:?}`")
                }
            }
        }
    }

    fn check_terminator(
        &mut self,
        pcx: &mut PureCtxt,
        env: &mut TypeEnv,
        terminator: &Terminator,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => self.check_ret(pcx, env),
            TerminatorKind::Goto { target } => Ok(vec![(*target, None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                self.check_switch_int(env, discr, targets)
            }
            TerminatorKind::Call { func, substs, args, destination } => {
                self.check_call(pcx, env, terminator.source_info, *func, substs, args, destination)
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

    fn check_ret(
        &mut self,
        pcx: &mut PureCtxt,
        env: &mut TypeEnv,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        let ret_place_ty = env.lookup_local(RETURN_PLACE);
        let mut gen = ConstraintGen::new(self.genv, pcx.breadcrumb(), Tag::Ret);

        gen.subtyping(&ret_place_ty, &self.ret);

        for constr in &self.ensures {
            gen.check_constr(env, constr);
        }
        Ok(vec![])
    }

    fn check_call(
        &mut self,
        pcx: &mut PureCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        func: DefId,
        substs: &[core::Ty],
        args: &[Operand],
        destination: &Option<(Place, BasicBlock)>,
    ) -> Result<Vec<(BasicBlock, Option<Expr>)>, ErrorReported> {
        let fn_sig = self.genv.lookup_fn_sig(func);

        let actuals = args
            .iter()
            .map(|arg| self.check_operand(env, arg))
            .collect_vec();

        let cx = LoweringCtxt::empty();
        let scope = pcx.scope();
        let mut fresh_kvar = |bty: &BaseTy| self.mode.fresh_kvar(self.genv.sort(bty), scope.iter());
        let substs = substs
            .iter()
            .map(|ty| cx.lower_ty(ty, &mut fresh_kvar))
            .collect_vec();

        let mut subst = Subst::with_type_substs(&substs);
        if subst.infer_from_fn_call(env, &actuals, fn_sig).is_err() {
            self.sess
                .emit_err(errors::ParamInferenceError { span: source_info.span });
            return Err(ErrorReported);
        };
        let fn_sig = subst.subst_fn_sig(&fn_sig.value);

        let mut gen = ConstraintGen::new(self.genv, pcx.breadcrumb(), Tag::Call(source_info.span));

        for (actual, formal) in actuals.iter().zip(&fn_sig.args) {
            gen.subtyping(actual, formal);
        }

        for constr in &fn_sig.requires {
            gen.check_constr(env, constr);
        }

        for constr in &fn_sig.ensures {
            match constr {
                Constr::Type(loc, updated_ty) => {
                    let updated_ty = env.unpack_ty(self.genv, pcx, updated_ty);
                    let gen = &mut ConstraintGen::new(
                        self.genv,
                        pcx.breadcrumb(),
                        Tag::Call(source_info.span),
                    );
                    env.update_path(gen, *loc, updated_ty);
                }
                Constr::Pred(e) => pcx.push_pred(e.clone()),
            }
        }

        let mut successors = vec![];
        if let Some((p, bb)) = destination {
            let ret = env.unpack_ty(self.genv, pcx, &fn_sig.ret);
            let mut gen =
                ConstraintGen::new(self.genv, pcx.breadcrumb(), Tag::Call(source_info.span));
            env.write_place(&mut gen, p, ret);
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
                    if bits == 0 {
                        e.not()
                    } else {
                        e.clone()
                    }
                }
                TyKind::Refine(bty @ (BaseTy::Int(_) | BaseTy::Uint(_)), e) => {
                    Expr::binary_op(BinOp::Eq, e.clone(), Expr::from_bits(bty, bits))
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
            .reduce(|e1, e2| Expr::binary_op(BinOp::And, e1, e2));

        successors.push((targets.otherwise(), otherwise));

        Ok(successors)
    }

    fn check_successors(
        &mut self,
        mut pcx: PureCtxt,
        env: TypeEnv,
        src_info: SourceInfo,
        successors: Vec<(BasicBlock, Option<Expr>)>,
    ) -> Result<(), ErrorReported> {
        for (target, guard) in successors {
            let mut pcx = pcx.breadcrumb();
            let env = env.clone();
            if let Some(guard) = guard {
                pcx.push_pred(guard);
            }
            self.check_goto(pcx, env, Some(src_info), target)?;
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        pcx: PureCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        if self.body.is_join_point(target) {
            if M::check_goto_join_point(self, pcx, env, src_info, target) {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.check_basic_block(pcx, env, target)
        }
    }

    fn check_rvalue(
        &self,
        pcx: &mut PureCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        rvalue: &Rvalue,
    ) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(pcx, env, source_info, *bin_op, op1, op2)
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
        pcx: &mut PureCtxt,
        env: &mut TypeEnv,
        source_info: SourceInfo,
        bin_op: ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.check_operand(env, op1);
        let ty2 = self.check_operand(env, op2);

        match bin_op {
            ir::BinOp::Eq => self.check_eq(BinOp::Eq, &ty1, &ty2),
            ir::BinOp::Ne => self.check_eq(BinOp::Ne, &ty1, &ty2),
            ir::BinOp::Add => self.check_arith_op(pcx, source_info, BinOp::Add, &ty1, &ty2),
            ir::BinOp::Sub => self.check_arith_op(pcx, source_info, BinOp::Sub, &ty1, &ty2),
            ir::BinOp::Mul => self.check_arith_op(pcx, source_info, BinOp::Mul, &ty1, &ty2),
            ir::BinOp::Div => self.check_arith_op(pcx, source_info, BinOp::Div, &ty1, &ty2),
            ir::BinOp::Rem => self.check_rem(pcx, source_info, &ty1, &ty2),
            ir::BinOp::Gt => self.check_cmp_op(BinOp::Gt, &ty1, &ty2),
            ir::BinOp::Ge => self.check_cmp_op(BinOp::Ge, &ty1, &ty2),
            ir::BinOp::Lt => self.check_cmp_op(BinOp::Lt, &ty1, &ty2),
            ir::BinOp::Le => self.check_cmp_op(BinOp::Le, &ty1, &ty2),
            ir::BinOp::BitAnd => self.check_bitwise_op(BinOp::And, &ty1, &ty2),
        }
    }

    fn check_bitwise_op(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(BaseTy::Int(int_ty1), _), TyKind::Refine(BaseTy::Int(int_ty2), _)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                Ty::exists(BaseTy::Int(*int_ty1), Pred::tt())
            }
            (
                TyKind::Refine(BaseTy::Uint(uint_ty1), _),
                TyKind::Refine(BaseTy::Uint(uint_ty2), _),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                Ty::exists(BaseTy::Uint(*uint_ty1), Pred::tt())
            }
            (TyKind::Refine(BaseTy::Bool, e1), TyKind::Refine(BaseTy::Bool, e2)) => {
                Ty::refine(BaseTy::Bool, Expr::binary_op(op, e1.clone(), e2.clone()))
            }
            _ => unreachable!("non-boolean arguments to bitwise op: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    // Rem is a special case due to differing semantics with negative numbers
    fn check_rem(&self, pcx: &mut PureCtxt, source_info: SourceInfo, ty1: &Ty, ty2: &Ty) -> Ty {
        let mut gen = ConstraintGen::new(self.genv, pcx.breadcrumb(), Tag::Rem(source_info.span));
        let ty = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

                let bty = BaseTy::Int(*int_ty1);
                let binding = Expr::binary_op(
                    BinOp::Eq,
                    Var::Bound,
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
                TyKind::Refine(BaseTy::Uint(uint_ty1), e1),
                TyKind::Refine(BaseTy::Uint(uint_ty2), e2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

                Ty::refine(
                    BaseTy::Uint(*uint_ty1),
                    Expr::binary_op(BinOp::Mod, e1.clone(), e2.clone()),
                )
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };

        ty
    }

    fn check_arith_op(
        &self,
        pcx: &mut PureCtxt,
        source_info: SourceInfo,
        op: BinOp,
        ty1: &Ty,
        ty2: &Ty,
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
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                return Ty::float(*float_ty1);
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        if matches!(op, BinOp::Div) {
            let mut gen =
                ConstraintGen::new(self.genv, pcx.breadcrumb(), Tag::Div(source_info.span));
            gen.check_pred(Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));
        }
        Ty::refine(bty, Expr::binary_op(op, e1, e2))
    }

    fn check_cmp_op(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
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
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                return Ty::exists(BaseTy::Bool, Pred::tt());
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        Ty::refine(BaseTy::Bool, Expr::binary_op(op, e1, e2))
    }

    fn check_eq(&self, op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                Ty::refine(BaseTy::Bool, Expr::binary_op(op, e1.clone(), e2.clone()))
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ty::exists(BaseTy::Bool, Pred::tt())
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_unary_op(&self, env: &mut TypeEnv, un_op: ir::UnOp, op: &Operand) -> Ty {
        let ty = self.check_operand(env, op);
        match un_op {
            ir::UnOp::Not => {
                match ty.kind() {
                    TyKind::Refine(BaseTy::Bool, e) => Ty::refine(BaseTy::Bool, e.not()),
                    _ => unreachable!("incompatible type: `{:?}`", ty),
                }
            }
            ir::UnOp::Neg => {
                match ty.kind() {
                    TyKind::Refine(BaseTy::Int(int_ty), e) => {
                        Ty::refine(BaseTy::Int(*int_ty), e.neg())
                    }
                    TyKind::Float(float_ty) => Ty::float(*float_ty),
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
                let expr = Expr::constant(ty::Constant::from(*n));
                Ty::refine(BaseTy::Int(*int_ty), expr)
            }
            Constant::Uint(n, uint_ty) => {
                let expr = Expr::constant(ty::Constant::from(*n));
                Ty::refine(BaseTy::Uint(*uint_ty), expr)
            }
            Constant::Bool(b) => {
                let expr = Expr::constant(ty::Constant::from(*b));
                Ty::refine(BaseTy::Bool, expr)
            }
            Constant::Float(_, float_ty) => Ty::float(*float_ty),
        }
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
    }
}

impl Mode for Inference<'_> {
    fn enter_basic_block(&mut self, pcx: &mut PureCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter(pcx)
    }

    fn check_goto_join_point(
        ck: &mut Checker<Inference>,
        _pcx: PureCtxt,
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
                entry.insert(env.into_infer(ck.genv, scope));
                true
            }
        };
        dbg::infer_goto_exit!(target, ck.mode.bb_envs[&target]);

        modified
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
    fn enter_basic_block(&mut self, pcx: &mut PureCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter(pcx)
    }

    fn check_goto_join_point(
        ck: &mut Checker<Check>,
        mut pcx: PureCtxt,
        env: TypeEnv,
        src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> bool {
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();
        let fresh_kvar = &mut |var, sort, params: &[Param]| {
            ck.mode.kvars.fresh(
                var,
                sort,
                scope
                    .iter()
                    .chain(params.iter().map(|param| (param.name, param.sort.clone()))),
            )
        };
        let mut first = false;
        let bb_env = ck.mode.bb_envs.entry(target).or_insert_with(|| {
            first = true;
            ck.mode
                .bb_envs_infer
                .remove(&target)
                .unwrap()
                .into_bb_env(ck.genv, fresh_kvar, &env)
        });

        dbg::check_goto!(target, pcx, env, bb_env);

        let tag = Tag::Goto(src_info.map(|s| s.span), target);
        let mut gen = ConstraintGen::new(ck.genv, pcx.breadcrumb(), tag);
        env.check_goto(&mut gen, bb_env);

        first
    }

    fn fresh_kvar<I>(&mut self, sort: Sort, scope: I) -> Pred
    where
        I: IntoIterator<Item = (Name, Sort)>,
    {
        self.kvars.fresh(Var::Bound, sort, scope)
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
