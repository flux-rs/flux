#![feature(rustc_private)]
#![feature(const_panic)]

extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_serialize;

pub mod bblock_env;
mod binding_tree;
pub mod local_env;

pub use bblock_env::BBlockEnv;
use itertools::Itertools;
use local_env::LocalEnv;

use liquid_rust_common::index::{Idx, IndexGen, IndexVec};
use liquid_rust_fixpoint::{Fixpoint, Safeness};
use liquid_rust_lrir::{
    mir::{
        BasicBlock, BasicBlockData, BinOp, Body, Local, Operand, PlaceRef, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{
        self, refiner::Refiner, subst::Subst, BaseTy, FnDecl, KVid, Path, Pred, Ty, TyCtxt, TyKind,
        Var,
    },
};

use rustc_middle::mir;
use rustc_mir::dataflow::{self, impls::MaybeUninitializedPlaces, move_paths::MoveData};

pub struct Checker<'a> {
    tcx: &'a TyCtxt,
    bb_envs: IndexVec<BasicBlock, BBlockEnv>,
    ret_env: BBlockEnv,
}

impl<'a> Checker<'a> {
    pub fn check<'tcx>(task: CheckingTask<'a, 'tcx>, tcx: &'a TyCtxt) -> CheckingResult {
        let kvid_gen = IndexGen::new();
        let ghost_gen = IndexGen::new();

        let mut env = LocalEnv::new(tcx, &ghost_gen);

        let mut subst = Subst::new();
        let mut vars_in_scope = vec![];
        for (gv, ty) in &task.fn_decl.requires {
            let fresh_gv = env.fresh_ghost();
            env.push_binding(fresh_gv, subst.apply(ty, tcx));
            vars_in_scope.push(Var::from(fresh_gv));
            subst.add_ghost_var_subst(*gv, fresh_gv);
        }
        for (local, gv) in task.body.args_iter().zip(&task.fn_decl.inputs) {
            env.insert_local(local, subst.apply(gv, tcx));
        }
        for local in task.body.vars_and_temps_iter() {
            let ty = Refiner::uninit(tcx, task.body.local_decls[local].ty);
            env.alloc(local, ty);
        }
        // FIXME: put ret_place = Local::new(0) somewhere else.
        let ret_place = Local::new(0);
        let ret_ty = Refiner::uninit(tcx, task.body.local_decls[ret_place].ty);
        env.alloc(ret_place, ret_ty);

        let bb_envs = (0..task.body.basic_blocks.len())
            .map(|i| {
                let bb = mir::BasicBlock::from_usize(i);
                let refiner = task.refiner_for_block(tcx, &kvid_gen, bb);
                BBlockEnv::new(
                    &task.body.local_decls,
                    refiner,
                    &mut vars_in_scope,
                    &ghost_gen,
                )
            })
            .collect();

        let ret_env = BBlockEnv {
            ghost_vars: task
                .fn_decl
                .ensures
                .iter()
                .map(|(gv, ty)| (*gv, subst.apply(ty, tcx)))
                .collect(),
            locals: vec![(ret_place, subst.apply(&task.fn_decl.output, tcx))],
        };

        let checker = Checker {
            tcx,
            bb_envs,
            ret_env,
        };

        // FIXME: Checking a jump to bb0 is redundant because its BBlockEnv is always going
        // to be "equivalent" to the LocalEnv initialized above. I think this is going to be
        // naturally fixed once we implement type checking considering the dominator tree.
        let bb0 = BasicBlock::new(0);
        checker.check_goto(&checker.bb_envs[bb0], &mut env);
        for (bb, bb_data) in task.body.basic_blocks.iter_enumerated() {
            checker.check_basic_block(bb, bb_data, &mut env);
        }

        let file = std::fs::File::create("binding_tree.dot").unwrap();
        env.bindings.dot(file).unwrap();

        let constraint = env.bindings.gen_constraint();
        match Fixpoint::default().check(constraint).tag {
            Safeness::Safe => CheckingResult { ok: true },
            _ => CheckingResult { ok: false },
        }
    }

    fn check_basic_block(&self, bb: BasicBlock, bb_data: &BasicBlockData, env: &mut LocalEnv) {
        let bb_env = &self.bb_envs[bb];

        env.enter_basic_block(bb_env, |env| {
            for statement in &bb_data.statements {
                self.check_statement(statement, env);
            }
            self.check_terminator(&bb_data.terminator, env);
        });
    }

    fn check_statement(&self, statement: &Statement, env: &mut LocalEnv) {
        match &statement.kind {
            StatementKind::Assign(place, rvalue) => {
                // FIXME: check ownership safety
                let ty = self.check_rvalue(rvalue, env);
                env.update(place.as_ref(), ty);
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
        }
    }

    fn check_terminator(&self, terminator: &Terminator, env: &mut LocalEnv) {
        #![allow(clippy::or_fun_call)]

        let tcx = self.tcx;
        match &terminator.kind {
            TerminatorKind::Goto { target } | TerminatorKind::Assert { target, .. } => {
                self.check_goto(&self.bb_envs[*target], env);
            }
            TerminatorKind::SwitchInt {
                discr,
                switch_ty,
                targets,
            } => {
                let (discr, ty) = self.check_operand(discr, env);
                assert!(matches!(ty.kind(), TyKind::Refined(bty, ..) if bty == switch_ty));
                for (bits, target) in targets.iter() {
                    let constant = tcx.mk_const_from_bits(bits, *switch_ty);
                    let guard = tcx.mk_bin_op(ty::BinOp::Eq, discr.clone(), constant);
                    env.with_guard(guard, |env| {
                        self.check_goto(&self.bb_envs[target], env);
                    });
                }
                let guard = targets
                    .iter()
                    .map(|(bits, _)| {
                        let v = tcx.mk_const_from_bits(bits, *switch_ty);
                        tcx.mk_un_op(
                            ty::UnOp::Not,
                            tcx.mk_bin_op(ty::BinOp::Eq, discr.clone(), v),
                        )
                    })
                    .fold1(|p1, p2| tcx.mk_bin_op(ty::BinOp::And, p1, p2))
                    .unwrap_or(tcx.preds.tt());
                env.with_guard(guard, |env| {
                    self.check_goto(&self.bb_envs[targets.otherwise()], env);
                });
            }
            TerminatorKind::Return => {
                self.check_goto(&self.ret_env, env);
            }
            TerminatorKind::Call { .. } => todo!(),
        }
    }

    fn check_goto(&self, bb_env: &BBlockEnv, env: &mut LocalEnv) {
        let subst = env.infer_subst(bb_env);
        let bb_env = subst.apply(bb_env, self.tcx);

        for &(local, gv) in &bb_env.locals {
            let ty1 = &self
                .tcx
                .selfify(&env.lookup(PlaceRef::from(local)), Path::from(gv));
            let ty2 = &bb_env.ghost_vars[&gv];
            env.subtyping(ty1, ty2);
        }
    }

    fn check_rvalue(&self, rvalue: &Rvalue, env: &mut LocalEnv) -> Ty {
        let tcx = self.tcx;
        match rvalue {
            Rvalue::Use(op) => self.check_operand(op, env).1,
            Rvalue::Ref(_, _, _) => todo!(),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                let (op1, ty1) = self.check_operand(op1, env);
                let (op2, ty2) = self.check_operand(op2, env);
                let ty_bin_op = match bin_op {
                    BinOp::Add => Some(ty::BinOp::Add),
                    BinOp::Sub => Some(ty::BinOp::Sub),
                    BinOp::Eq => Some(ty::BinOp::Eq),
                    BinOp::Lt => Some(ty::BinOp::Lt),
                    BinOp::Le => Some(ty::BinOp::Lte),
                    BinOp::Ne => Some(ty::BinOp::Neq),
                    BinOp::Ge => Some(ty::BinOp::Gte),
                    BinOp::Gt => Some(ty::BinOp::Gt),
                    BinOp::Mul => Some(ty::BinOp::Mul),
                    BinOp::Div => Some(ty::BinOp::Div),
                    BinOp::Rem => Some(ty::BinOp::Rem),
                    BinOp::BitXor
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::Offset => None,
                };
                let ret_ty = match bin_op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::BitXor
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::Shl
                    | BinOp::Shr => {
                        assert!(ty1.is_int() && ty2.is_int());
                        BaseTy::Int
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        assert!(ty1.is_int() && ty2.is_int());
                        BaseTy::Bool
                    }
                    // FIXME: we should check that the operation and operands have the same base type
                    BinOp::Eq | BinOp::Ne => BaseTy::Bool,
                    BinOp::Offset => todo!(),
                };
                let refine = if let Some(ty_bin_op) = ty_bin_op {
                    tcx.mk_bin_op(
                        ty::BinOp::Eq,
                        tcx.preds.nu(),
                        tcx.mk_bin_op(ty_bin_op, op1, op2),
                    )
                } else {
                    tcx.preds.tt()
                };
                tcx.mk_refine(ret_ty, refine)
            }
            Rvalue::UnaryOp(un_op, op) => {
                let (op, ty) = self.check_operand(op, env);
                let (ret_ty, un_op) = match un_op {
                    UnOp::Not => {
                        assert!(ty.is_bool());
                        (BaseTy::Bool, ty::UnOp::Not)
                    }
                    UnOp::Neg => {
                        assert!(ty.is_int());
                        (BaseTy::Int, ty::UnOp::Neg)
                    }
                };
                let pred = tcx.mk_bin_op(ty::BinOp::Eq, tcx.preds.nu(), tcx.mk_un_op(un_op, op));
                tcx.mk_refine(ret_ty, pred)
            }
        }
    }

    fn check_operand(&self, op: &Operand, env: &mut LocalEnv) -> (Pred, Ty) {
        let tcx = self.tcx;
        match op {
            Operand::Copy(place) => {
                let ty = env.lookup(place.as_ref());
                let path = env.current_path(place.as_ref());
                assert!(ty.is_copy());
                (tcx.mk_path(path.clone()), tcx.selfify(&ty, path))
            }
            Operand::Move(place) => {
                // FIXME: check ownership safety
                let path = env.current_path(place.as_ref());
                let ty = env.move_place(place.as_ref());
                (tcx.mk_path(path.clone()), tcx.selfify(&ty, path))
            }
            &Operand::Constant(c) => {
                let refine = tcx.mk_bin_op(
                    ty::BinOp::Eq,
                    tcx.preds.nu(),
                    tcx.mk_const_from_bits(c.bits(), c.ty()),
                );
                (
                    tcx.mk_const_from_bits(c.bits(), c.ty()),
                    tcx.mk_refine(c.ty(), refine),
                )
            }
        }
    }
}

pub struct CheckingTask<'a, 'tcx> {
    body: &'a Body<'tcx>,
    fn_decl: &'a FnDecl,
    move_data: MoveData<'tcx>,
    flow_uninit: dataflow::Results<'tcx, MaybeUninitializedPlaces<'a, 'tcx>>,
}

impl<'a, 'tcx> CheckingTask<'a, 'tcx> {
    pub fn new(
        body: &'a Body<'tcx>,
        fn_decl: &'a FnDecl,
        move_data: MoveData<'tcx>,
        flow_uninit: dataflow::Results<'tcx, MaybeUninitializedPlaces<'a, 'tcx>>,
    ) -> Self {
        Self {
            body,
            fn_decl,
            move_data,
            flow_uninit,
        }
    }

    fn refiner_for_block<'b>(
        &'b self,
        tcx: &'b TyCtxt,
        kvid_gen: &'b IndexGen<KVid>,
        bb: mir::BasicBlock,
    ) -> Refiner {
        Refiner::new(
            tcx,
            &self.move_data,
            self.flow_uninit.entry_set_for_block(bb),
            kvid_gen,
        )
    }
}

pub struct CheckingResult {
    pub ok: bool,
}
