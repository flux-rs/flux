#![feature(rustc_private, min_specialization, once_cell)]
#![allow(warnings)]

extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

mod constraint_builder;
pub mod global_env;
mod inference;
mod intern;
mod lowering;
pub mod subst;
pub mod ty;
mod tyenv;

use crate::{
    constraint_builder::{ConstraintBuilder, Cursor},
    inference::InferCtxt,
    lowering::LowerCtxt,
    subst::Subst,
    ty::{BaseTy, BinOp, Expr, ExprKind, KVid, RVid, Region, Ty, TyKind, Var},
};
use global_env::GlobalEnv;
use itertools::Itertools;
use liquid_rust_common::{
    disjoint_sets::DisjointSetsMap,
    errors::ErrorReported,
    index::{Idx, IndexGen},
};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Local, Operand, Rvalue, SourceInfo, Statement,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
    },
    ty::{self as core, Name},
};
use liquid_rust_fixpoint::Fixpoint;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_session::Session;
use rustc_span::MultiSpan;
use tyenv::TyEnv;

pub struct Checker<'a, 'tcx> {
    sess: &'a Session,
    body: &'a Body<'tcx>,
    // All join points immediatly dominated by a block.
    dominated_join_points: FxHashMap<BasicBlock, Vec<BasicBlock>>,
    visited: BitSet<BasicBlock>,
    bb_envs: FxHashMap<BasicBlock, TyEnv>,
    bb_env_shapes: FxHashMap<BasicBlock, DisjointSetsMap<RVid, inference::Ty>>,
    ret_ty: Ty,
    global_env: &'a GlobalEnv,
    name_gen: &'a IndexGen<Var>,
    kvid_gen: &'a IndexGen<KVid>,
    ensures: Vec<(Region, Ty)>,
}

impl Checker<'_, '_> {
    pub fn check(
        global_env: &GlobalEnv,
        sess: &Session,
        body: &Body,
        fn_sig: &core::FnSig,
    ) -> Result<(), ErrorReported> {
        let bb_env_shapes = InferCtxt::infer(global_env, body, fn_sig);
        let rvid_gen = &IndexGen::new();
        rvid_gen.skip(body.local_decls.len());

        let mut constraint = ConstraintBuilder::new();

        let name_gen = &IndexGen::new();
        let (params, requires, args, ret_ty, ensures) =
            LowerCtxt::lower_with_fresh_names(name_gen, rvid_gen, fn_sig);

        let mut env = TyEnv::new();

        let mut cursor = constraint.as_cursor();
        for (var, sort, pred) in params {
            cursor.push_forall(var, sort, pred);
        }

        // Return place
        env.push_region(TyKind::Uninit.intern());

        // Arguments
        for ty in args {
            env.push_region(cursor.unpack(name_gen, ty));
        }

        // Vars and temps
        for _ in body.vars_and_temps_iter() {
            env.push_region(TyKind::Uninit.intern());
        }

        // Requires
        for ty in requires {
            env.push_region(ty);
        }

        let dominators = body.dominators();
        let mut dominated_join_points = FxHashMap::<BasicBlock, Vec<BasicBlock>>::default();
        for bb in body.join_points() {
            dominated_join_points
                .entry(dominators.immediate_dominator(bb))
                .or_default()
                .push(bb);
        }

        let mut checker = Checker {
            sess,
            global_env,
            body,
            dominated_join_points,
            bb_envs: FxHashMap::default(),
            visited: BitSet::new_empty(body.basic_blocks.len()),
            bb_env_shapes,
            ret_ty,
            name_gen,
            kvid_gen: &IndexGen::new(),
            ensures,
        };

        checker.check_goto(&mut env, &mut cursor, START_BLOCK)?;
        for bb in body.reverse_postorder() {
            if !checker.visited.contains(bb) {
                let mut env = checker.bb_envs.get(&bb).unwrap().clone();
                env.unpack(&mut cursor, name_gen);
                checker.check_basic_block(&mut env, &mut cursor, bb)?;
            }
        }
        println!("{:?}", constraint);
        let constraint = constraint.to_fixpoint(name_gen);
        println!("{:?}", Fixpoint::check(&constraint));
        Ok(())
    }

    fn check_basic_block(
        &mut self,
        env: &mut TyEnv,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        self.visited.insert(bb);

        self.dominated_join_points
            .get(&bb)
            .iter()
            .copied()
            .flatten()
            .for_each(|bb| {
                let shape = self.bb_env_shapes.remove(bb).unwrap();
                let bb_env = env.infer_bb_env(cursor, shape, self.name_gen);
                self.bb_envs.insert(*bb, bb_env);
            });

        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(env, cursor, stmt);
        }
        if let Some(terminator) = &data.terminator {
            self.check_terminator(env, cursor, terminator)?;
        }
        Ok(())
    }

    fn check_statement(&self, env: &mut TyEnv, cursor: &mut Cursor, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(p, rvalue) => {
                let ty = self.check_rvalue(env, rvalue);
                // OWNERSHIP SAFETY CHECK
                env.write_place(cursor, p, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(
        &mut self,
        env: &mut TyEnv,
        cursor: &mut Cursor,
        terminator: &Terminator,
    ) -> Result<(), ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = env.lookup_region(RVid::from(RETURN_PLACE));
                cursor
                    .snapshot()
                    .subtyping(ret_place_ty, self.ret_ty.clone());

                for (region, ensured_ty) in &self.ensures {
                    let actual_ty = env.lookup_region(region[0]);
                    cursor.snapshot().subtyping(actual_ty, ensured_ty.clone());
                }
            }
            TerminatorKind::Goto { target } => {
                self.check_goto(env, cursor, *target)?;
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.check_operand(env, discr);
                match discr_ty.kind() {
                    TyKind::Refine(BaseTy::Bool, discr_expr) => {
                        for (bits, bb) in targets.iter() {
                            let cursor = &mut cursor.snapshot();
                            cursor.push_guard(if bits != 0 {
                                discr_expr.clone()
                            } else {
                                discr_expr.not()
                            });
                            self.check_goto(&mut env.clone(), cursor, bb)?;
                        }
                        let otherwise = targets
                            .iter()
                            .map(|(bits, _)| {
                                if bits != 0 {
                                    discr_expr.not()
                                } else {
                                    discr_expr.clone()
                                }
                            })
                            .reduce(|e1, e2| ExprKind::BinaryOp(BinOp::And, e1, e2).intern());

                        let cursor = &mut cursor.snapshot();
                        if let Some(otherwise) = otherwise {
                            cursor.push_guard(otherwise);
                        }

                        self.check_goto(env, cursor, targets.otherwise())?;
                    }
                    TyKind::Refine(BaseTy::Int(_), _) => {
                        todo!("switch_int not implemented for integer discriminants")
                    }
                    _ => unreachable!("discr with incompatible type"),
                };
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);
                let actuals = args
                    .iter()
                    .map(|arg| self.check_operand(env, arg))
                    .collect_vec();

                let (subst, region_subst) = self.infer_subst(
                    terminator.source_info,
                    env,
                    &actuals,
                    &fn_sig.requires,
                    &fn_sig.args,
                )?;
                self.check_subst(&subst, &fn_sig.params, terminator.source_info)?;

                let (params, requires, formals, ret, ensures) =
                    LowerCtxt::lower_with_subst(self.name_gen, subst, &region_subst, fn_sig);
                for pred in params {
                    cursor.push_head(pred);
                }
                for (actual, formal) in actuals.into_iter().zip(formals) {
                    cursor.snapshot().subtyping(actual, formal);
                }
                for (region, required_ty) in requires {
                    let actual_ty = env.lookup_region(region[0]);
                    cursor.snapshot().subtyping(actual_ty, required_ty);
                }

                for (region, updated_ty) in ensures {
                    env.update_region(cursor, region[0], updated_ty);
                }

                if let Some((p, bb)) = destination {
                    let ret = cursor.unpack(self.name_gen, ret);

                    env.write_place(cursor, p, ret);
                    self.check_goto(env, cursor, *bb)?;
                }
            }
        }
        Ok(())
    }

    fn check_goto(
        &mut self,
        env: &mut TyEnv,
        cursor: &mut Cursor,
        target: BasicBlock,
    ) -> Result<(), ErrorReported> {
        if self.body.is_join_point(target) {
            let bb_env = &self.bb_envs[&target];
            for (mut region, ty1) in env.iter() {
                // FIXME: we should check the region in env is a subset of a region in bb_env
                let local = region.next().unwrap();
                let ty2 = bb_env.lookup_region(local);
                cursor.subtyping(ty1, ty2);
            }
            Ok(())
        } else {
            self.check_basic_block(env, cursor, target)
        }
    }

    fn check_rvalue(&self, env: &mut TyEnv, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => self.check_binary_op(env, bin_op, op1, op2),
            Rvalue::MutRef(place) => {
                // OWNERSHIP SAFETY CHECK
                TyKind::MutRef(env.get_region(place)).intern()
            }
            Rvalue::UnaryOp(un_op, op) => self.check_unary_op(env, *un_op, op),
        }
    }

    fn check_binary_op(
        &self,
        env: &mut TyEnv,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.check_operand(env, op1);
        let ty2 = self.check_operand(env, op2);

        match bin_op {
            ir::BinOp::Add => self.check_num_op(BinOp::Add, ty1, ty2),
            ir::BinOp::Sub => self.check_num_op(BinOp::Sub, ty1, ty2),
            ir::BinOp::Gt => self.check_cmp(BinOp::Gt, ty1, ty2),
            ir::BinOp::Lt => self.check_cmp(BinOp::Lt, ty1, ty2),
        }
    }

    fn check_num_op(&self, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                TyKind::Refine(
                    BaseTy::Int(*int_ty1),
                    ExprKind::BinaryOp(op, e1.clone(), e2.clone()).intern(),
                )
                .intern()
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_cmp(&self, op: BinOp, ty1: Ty, ty2: Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Refine(BaseTy::Int(int_ty1), e1),
                TyKind::Refine(BaseTy::Int(int_ty2), e2),
            ) => {
                debug_assert_eq!(int_ty1, int_ty2);
                TyKind::Refine(
                    BaseTy::Bool,
                    ExprKind::BinaryOp(op, e1.clone(), e2.clone()).intern(),
                )
                .intern()
            }
            _ => unreachable!("incompatible types: `{:?}` `{:?}`", ty1, ty2),
        }
    }

    fn check_unary_op(&self, env: &mut TyEnv, un_op: ir::UnOp, op: &Operand) -> Ty {
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

    fn check_operand(&self, env: &mut TyEnv, operand: &Operand) -> Ty {
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
            Constant::Bool(b) => {
                let expr = ExprKind::Constant(ty::Constant::from(*b)).intern();
                TyKind::Refine(BaseTy::Bool, expr).intern()
            }
        }
    }

    fn infer_subst(
        &self,
        source_info: SourceInfo,
        env: &TyEnv,
        actuals: &[Ty],
        requires: &[(core::Ident, core::Ty)],
        formals: &[core::Ty],
    ) -> Result<(FxHashMap<Name, Expr>, FxHashMap<Name, Region>), ErrorReported> {
        assert!(actuals.len() == formals.len());

        let mut subst = FxHashMap::default();
        let mut region_subst = FxHashMap::default();
        for (actual, formal) in actuals.iter().zip(formals) {
            match (actual.kind(), formal) {
                (
                    TyKind::Refine(bty1, e),
                    core::Ty::Refine(
                        bty2,
                        core::Expr {
                            kind: core::ExprKind::Var(ident),
                            ..
                        },
                    ),
                ) => {
                    debug_assert!(bty1 == bty2);
                    match subst.insert(ident.name, e.clone()) {
                        Some(old_e) if &old_e != e => {
                            let mut s = MultiSpan::from_span(source_info.span);
                            s.push_span_label(
                                source_info.span,
                                format!("abiguous instantiation for parameter `{}`", ident.symbol),
                            );
                            self.sess.span_err(s, "parameter inference failed");
                            return Err(ErrorReported);
                        }
                        _ => {}
                    }
                }
                (TyKind::MutRef(region1), core::Ty::MutRef(region2)) => {
                    match region_subst.insert(region2.name, region1.clone()) {
                        Some(old_region) if &old_region != region1 => {
                            let mut s = MultiSpan::from_span(source_info.span);
                            s.push_span_label(
                                source_info.span,
                                format!(
                                    "abiguous instantiation for region parameter `{}`",
                                    region2.symbol
                                ),
                            );
                            self.sess.span_err(s, "parameter inference failed");
                            return Err(ErrorReported);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        for (region, required) in requires {
            let actual = env.lookup_region(region_subst[&region.name][0]);
            match (actual.kind(), required) {
                (
                    TyKind::Refine(bty1, e),
                    core::Ty::Refine(
                        bty2,
                        core::Expr {
                            kind: core::ExprKind::Var(ident),
                            ..
                        },
                    ),
                ) => {
                    debug_assert!(bty1 == bty2);
                    match subst.insert(ident.name, e.clone()) {
                        Some(old_e) if &old_e != e => {
                            let mut s = MultiSpan::from_span(source_info.span);
                            s.push_span_label(
                                source_info.span,
                                format!("abiguous instantiation for parameter `{}`", ident.symbol),
                            );
                            self.sess.span_err(s, "parameter inference failed");
                            return Err(ErrorReported);
                        }
                        _ => {}
                    }
                }
                (TyKind::MutRef(region1), core::Ty::MutRef(region2)) => {
                    match region_subst.insert(region2.name, region1.clone()) {
                        Some(old_region) if &old_region != region1 => {
                            let mut s = MultiSpan::from_span(source_info.span);
                            s.push_span_label(
                                source_info.span,
                                format!(
                                    "abiguous instantiation for region parameter `{}`",
                                    region2.symbol
                                ),
                            );
                            self.sess.span_err(s, "parameter inference failed");
                            return Err(ErrorReported);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Ok((subst, region_subst))
    }

    fn check_subst(
        &self,
        subst: &FxHashMap<Name, Expr>,
        params: &[core::Param],
        source_info: SourceInfo,
    ) -> Result<(), ErrorReported> {
        for param in params {
            if !subst.contains_key(&param.name.name) {
                let mut s = MultiSpan::from_span(source_info.span);
                s.push_span_label(
                    source_info.span,
                    format!(
                        "cannot infer the value of parameter `{}` in this function call",
                        param.name.symbol
                    ),
                );
                s.push_span_label(
                    param.name.span,
                    format!("parameter `{}` declared here", param.name.symbol),
                );
                self.sess.span_err(s, "parameter inference failed");
                return Err(ErrorReported);
            }
        }
        Ok(())
    }
}
