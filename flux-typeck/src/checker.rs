extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{hash_map::Entry, BinaryHeap};

use flux_common::{config::AssertBehavior, index::IndexVec};
use flux_middle::{
    global_env::GlobalEnv,
    rustc::{
        self,
        mir::{
            self, AggregateKind, BasicBlock, Body, Constant, Operand, Place, Rvalue, SourceInfo,
            Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
    },
    ty::{
        self, BaseTy, BinOp, Binders, BoundVar, Constraint, Constraints, Expr, FnSig, PolySig,
        Pred, RefKind, Sort, Ty, TyKind, VariantIdx,
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir as rustc_mir;

use crate::{
    constraint_gen::{ConstrGen, Tag},
    dbg,
    fixpoint::KVarStore,
    refine_tree::{RefineCtxt, RefineTree, Snapshot},
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
    ) -> bool;

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
    ) -> Result<FxHashMap<BasicBlock, TypeEnvInfer>, ErrorGuaranteed> {
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
    ) -> Result<RefineTree, ErrorGuaranteed> {
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
    ) -> Result<(), ErrorGuaranteed> {
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
                ty::Constraint::Type(path, ty) => {
                    assert!(path.projection().is_empty());
                    let ty = rcx.unpack(ty, false);
                    env.alloc_universal_loc(path.loc, ty);
                }
                ty::Constraint::Pred(e) => {
                    rcx.assume_pred(e.clone());
                }
            }
        }

        for (local, ty) in body.args_iter().zip(fn_sig.args()) {
            let ty = rcx.unpack(ty, false);
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
    ) -> Result<(), ErrorGuaranteed> {
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
    ) -> Result<(), ErrorGuaranteed> {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rcx, env, stmt.source_info, rvalue)?;
                let ty = rcx.unpack(&ty, false);
                let gen =
                    &mut self
                        .phase
                        .constr_gen(self.genv, rcx, Tag::Assign(stmt.source_info.span));
                env.write_place(rcx, gen, place, ty);
            }
            StatementKind::SetDiscriminant { .. } => {
                // TODO(nilehmann) double check here that the place is unfolded to
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
    ) -> Result<Vec<(BasicBlock, Guard)>, ErrorGuaranteed> {
        match &terminator.kind {
            TerminatorKind::Return => self.check_ret(rcx, env, src_info),
            TerminatorKind::Unreachable => Ok(vec![]),
            TerminatorKind::Goto { target } => Ok(vec![(*target, Guard::None)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.check_operand(rcx, env, terminator.source_info, discr);
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
                let fn_sig = self.genv.lookup_fn_sig(func_id);

                let ret =
                    self.check_call(rcx, env, terminator.source_info, fn_sig, substs, args)?;

                let ret = rcx.unpack(&ret, false);
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Call(terminator.source_info.span));
                env.write_place(rcx, &mut gen, destination, ret);

                if let Some(target) = target {
                    Ok(vec![(*target, Guard::None)])
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
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Fold(terminator.source_info.span));
                let _ = env.move_place(rcx, &mut gen, place);
                Ok(vec![(*target, Guard::None)])
            }
            TerminatorKind::DropAndReplace { place, value, target, .. } => {
                let ty = self.check_operand(rcx, env, terminator.source_info, value);
                let ty = rcx.unpack(&ty, false);
                let mut gen =
                    self.phase
                        .constr_gen(self.genv, rcx, Tag::Assign(terminator.source_info.span));
                env.write_place(rcx, &mut gen, place, ty);
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
    ) -> Result<Vec<(BasicBlock, Guard)>, ErrorGuaranteed> {
        let tag = match src_info {
            Some(info) => Tag::RetAt(info.span),
            None => Tag::Ret,
        };
        let gen = &mut self.phase.constr_gen(self.genv, rcx, tag);
        let ret_place_ty = env.lookup_place(rcx, gen, Place::RETURN);

        gen.subtyping(rcx, &ret_place_ty, &self.ret);

        for constraint in &self.ensures {
            gen.check_constraint(rcx, env, constraint);
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
    ) -> Result<Ty, ErrorGuaranteed> {
        let actuals = args
            .iter()
            .map(|op| self.check_operand(rcx, env, source_info, op))
            .collect_vec();

        let substs = substs
            .iter()
            .map(|arg| self.genv.refine_generic_arg(arg, &mut |_| Pred::Hole))
            .collect_vec();

        let output = self
            .phase
            .constr_gen(self.genv, rcx, Tag::Call(source_info.span))
            .check_fn_call(rcx, env, &fn_sig, &substs, &actuals)
            .map_err(|_| {
                self.genv
                    .sess
                    .emit_err(errors::ParamInferenceError { span: source_info.span })
            })?;

        for constr in &output.ensures {
            match constr {
                Constraint::Type(path, updated_ty) => {
                    let updated_ty = rcx.unpack(updated_ty, false);
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
        msg: &'static str,
    ) -> Guard {
        let ty = self.check_operand(rcx, env, source_info, cond);
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
            AssertBehavior::Ignore => Guard::None,
            AssertBehavior::Assume => Guard::Pred(pred),
            AssertBehavior::Check => {
                self.phase
                    .constr_gen(self.genv, rcx, Tag::Assert(msg, source_info.span))
                    .check_pred(rcx, pred.clone());

                Guard::Pred(pred)
            }
        }
    }

    fn check_if(discr_ty: &Ty, targets: &rustc_mir::SwitchTargets) -> Vec<(BasicBlock, Guard)> {
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
        let place = discr_ty.expect_discr();

        let mut successors = vec![];
        for (bits, bb) in targets.iter() {
            successors
                .push((bb, Guard::Match(place.clone(), VariantIdx::from_usize(bits as usize))));
        }
        successors.push((targets.otherwise(), Guard::None));

        successors
    }

    fn check_successors(
        &mut self,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        src_info: SourceInfo,
        successors: Vec<(BasicBlock, Guard)>,
    ) -> Result<(), ErrorGuaranteed> {
        for (target, guard) in successors {
            let mut rcx = rcx.breadcrumb();
            let mut env = env.clone();
            match guard {
                Guard::None => {}
                Guard::Pred(expr) => {
                    rcx.assume_pred(expr);
                }
                Guard::Match(place, variant_idx) => {
                    let tag = Tag::Goto(Some(src_info.span), target);
                    let gen = &mut self.phase.constr_gen(self.genv, &rcx, tag);
                    env.downcast(&mut rcx, gen, &place, variant_idx);
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
    ) -> Result<(), ErrorGuaranteed> {
        if self.is_exit_block(target) {
            self.check_ret(&mut rcx, &mut env, src_info)?;
            Ok(())
        } else if self.body.is_join_point(target) {
            if P::check_goto_join_point(self, rcx, env, src_info, target) {
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
    ) -> Result<Ty, ErrorGuaranteed> {
        match rvalue {
            Rvalue::Use(operand) => Ok(self.check_operand(rcx, env, src_info, operand)),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                Ok(self.check_binary_op(rcx, env, src_info, *bin_op, op1, op2))
            }
            Rvalue::MutRef(place) => {
                let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
                Ok(env.borrow(rcx, gen, RefKind::Mut, place))
            }
            Rvalue::ShrRef(place) => {
                let gen = &mut self.phase.constr_gen(self.genv, rcx, Tag::Other);
                Ok(env.borrow(rcx, gen, RefKind::Shr, place))
            }
            Rvalue::UnaryOp(un_op, op) => Ok(self.check_unary_op(rcx, env, src_info, *un_op, op)),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let sig = self.genv.variant_sig(*def_id, *variant_idx);
                self.check_call(rcx, env, src_info, sig, substs, args)
            }
            Rvalue::Discriminant(place) => Ok(Ty::discr(place.clone())),
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
        let ty1 = self.check_operand(rcx, env, source_info, op1);
        let ty2 = self.check_operand(rcx, env, source_info, op2);

        match bin_op {
            mir::BinOp::Eq => Self::check_eq(BinOp::Eq, &ty1, &ty2),
            mir::BinOp::Ne => Self::check_eq(BinOp::Ne, &ty1, &ty2),
            mir::BinOp::Add => self.check_arith_op(rcx, source_info, BinOp::Add, &ty1, &ty2),
            mir::BinOp::Sub => self.check_arith_op(rcx, source_info, BinOp::Sub, &ty1, &ty2),
            mir::BinOp::Mul => self.check_arith_op(rcx, source_info, BinOp::Mul, &ty1, &ty2),
            mir::BinOp::Div => self.check_arith_op(rcx, source_info, BinOp::Div, &ty1, &ty2),
            mir::BinOp::Rem => self.check_rem(rcx, source_info, &ty1, &ty2),
            mir::BinOp::Gt => Self::check_cmp_op(BinOp::Gt, &ty1, &ty2),
            mir::BinOp::Ge => Self::check_cmp_op(BinOp::Ge, &ty1, &ty2),
            mir::BinOp::Lt => Self::check_cmp_op(BinOp::Lt, &ty1, &ty2),
            mir::BinOp::Le => Self::check_cmp_op(BinOp::Le, &ty1, &ty2),
            mir::BinOp::BitAnd => Self::check_bitwise_op(BinOp::And, &ty1, &ty2),
        }
    }

    fn check_bitwise_op(op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), _),
                TyKind::Indexed(BaseTy::Int(int_ty2), _),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                Ty::exists(BaseTy::Int(*int_ty1), Binders::new(Pred::tt(), vec![Sort::Int]))
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), _),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), _),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                Ty::exists(BaseTy::Uint(*uint_ty1), Binders::new(Pred::tt(), vec![Sort::Int]))
            }
            (TyKind::Indexed(BaseTy::Bool, indices1), TyKind::Indexed(BaseTy::Bool, indices2)) => {
                let e = Expr::binary_op(op, indices1[0].expr.clone(), indices2[0].expr.clone());
                Ty::indexed(BaseTy::Bool, vec![e.into()])
            }
            _ => unreachable!("non-boolean arguments to bitwise op: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    // Rem is a special case due to differing semantics with negative numbers
    fn check_rem(
        &mut self,
        rcx: &mut RefineCtxt,
        source_info: SourceInfo,
        ty1: &Ty,
        ty2: &Ty,
    ) -> Ty {
        let gen = &mut self
            .phase
            .constr_gen(self.genv, rcx, Tag::Rem(source_info.span));
        let ty = match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Indexed(BaseTy::Int(int_ty1), exprs1),
                TyKind::Indexed(BaseTy::Int(int_ty2), exprs2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                let (e1, e2) = (&exprs1[0], &exprs2[0]);
                gen.check_pred(rcx, Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

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
                let expr = Expr::binary_op(BinOp::Imp, guard, binding);
                Ty::exists(bty, Binders::new(Pred::Expr(expr), vec![Sort::Int]))
            }
            (
                TyKind::Indexed(BaseTy::Uint(uint_ty1), indices1),
                TyKind::Indexed(BaseTy::Uint(uint_ty2), indices2),
            ) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                let (e1, e2) = (&indices1[0].expr, &indices2[0].expr);
                gen.check_pred(rcx, Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));

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
        &mut self,
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
            self.phase
                .constr_gen(self.genv, rcx, Tag::Div(source_info.span))
                .check_pred(rcx, Expr::binary_op(BinOp::Ne, e2.clone(), Expr::zero()));
        }
        Ty::indexed(bty, vec![Expr::binary_op(op, e1, e2).into()])
    }

    fn check_cmp_op(op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
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
                return Ty::exists(BaseTy::Bool, Binders::new(Pred::tt(), vec![Sort::Bool]));
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        };
        Ty::indexed(BaseTy::Bool, vec![Expr::binary_op(op, e1, e2).into()])
    }

    fn check_eq(op: BinOp, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, indices1), TyKind::Indexed(bty2, indices2)) => {
                debug_assert_eq!(bty1, bty2);
                let e = Expr::binary_op(op, indices1[0].clone(), indices2[0].clone());
                Ty::indexed(BaseTy::Bool, vec![e.into()])
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ty::exists(BaseTy::Bool, Binders::new(Pred::tt(), vec![Sort::Bool]))
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_unary_op(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        un_op: mir::UnOp,
        op: &Operand,
    ) -> Ty {
        let ty = self.check_operand(rcx, env, src_info, op);
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

    fn check_operand(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        src_info: SourceInfo,
        operand: &Operand,
    ) -> Ty {
        let ty = match operand {
            Operand::Copy(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self
                    .phase
                    .constr_gen(self.genv, rcx, Tag::Fold(src_info.span));
                env.lookup_place(rcx, gen, p)
            }
            Operand::Move(p) => {
                // OWNERSHIP SAFETY CHECK
                let gen = &mut self
                    .phase
                    .constr_gen(self.genv, rcx, Tag::Fold(src_info.span));
                env.move_place(rcx, gen, p)
            }
            Operand::Constant(c) => Self::check_constant(c),
        };
        rcx.unpack(&ty, false)
    }

    fn check_constant(c: &Constant) -> Ty {
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
            Constant::Str => Ty::mk_ref(RefKind::Shr, Ty::str()),
        }
    }

    #[track_caller]
    fn snapshot_at_dominator(&self, bb: BasicBlock) -> &Snapshot {
        let dominator = self.dominators.immediate_dominator(bb);
        self.snapshots[dominator].as_ref().unwrap()
    }
}

impl Phase for Inference<'_> {
    fn constr_gen<'a, 'rcx, 'tcx>(
        &'a mut self,
        genv: &'a GlobalEnv<'a, 'tcx>,
        _rcx: &RefineCtxt,
        tag: Tag,
    ) -> ConstrGen<'a, 'tcx> {
        ConstrGen::new(genv, |sorts| Binders::new(Pred::Hole, sorts), tag)
    }

    fn enter_basic_block(&mut self, _rcx: &mut RefineCtxt, bb: BasicBlock) -> TypeEnv {
        self.bb_envs[&bb].enter()
    }

    fn check_goto_join_point(
        ck: &mut Checker<Inference>,
        mut rcx: RefineCtxt,
        env: TypeEnv,
        _src_info: Option<SourceInfo>,
        target: BasicBlock,
    ) -> bool {
        // TODO(nilehmann) we should only ask for the scope in the vacant branch
        let scope = ck.snapshot_at_dominator(target).scope().unwrap();

        dbg::infer_goto_enter!(target, env, ck.phase.bb_envs.get(&target));
        let mut gen = ConstrGen::new(ck.genv, |sorts| Binders::new(Pred::Hole, sorts), Tag::Other);
        let modified = match ck.phase.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(&mut rcx, &mut gen, env),
            Entry::Vacant(entry) => {
                entry.insert(env.into_infer(&mut rcx, &mut gen, scope));
                true
            }
        };
        dbg::infer_goto_exit!(target, ck.phase.bb_envs[&target]);

        modified
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
        let fresh_kvar = move |sorts: &[Sort]| self.kvars.fresh(sorts, scope.iter());
        ConstrGen::new(genv, fresh_kvar, tag)
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
        let bb_env = &ck.phase.bb_envs[&target];
        debug_assert_eq!(&ck.snapshot_at_dominator(target).scope().unwrap(), bb_env.scope());

        dbg::check_goto!(target, rcx, env, bb_env);

        let fresh_kvar = |sorts: &[Sort]| ck.phase.kvars.fresh(sorts, bb_env.scope().iter());
        let tag = Tag::Goto(src_info.map(|s| s.span), target);
        let gen = &mut ConstrGen::new(ck.genv, fresh_kvar, tag);
        env.check_goto(&mut rcx, gen, bb_env);

        !ck.visited.contains(target)
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
    use flux_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error(refineck::param_inference_error, code = "FLUX")]
    pub struct ParamInferenceError {
        #[primary_span]
        pub span: Span,
    }
}
