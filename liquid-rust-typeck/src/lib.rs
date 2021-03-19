#![feature(rustc_private)]
#![feature(or_patterns)]

extern crate rustc_middle;
extern crate rustc_mir;

pub mod bblock_env;
mod binding_tree;
pub mod local_env;

pub use bblock_env::BBlockEnv;
use liquid_rust_common::index::{Index, IndexGen, IndexMap};
use liquid_rust_fixpoint::Fixpoint;
use liquid_rust_lrir::{
    mir::{
        BasicBlock, BasicBlockData, BinOp, Body, Constant, Local, Operand, PlaceRef, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{refiner::Refiner, subst::Subst, BaseTy, FnDecl, Path, Pred, Ty, TyCtxt, TyKind, Var},
};
use local_env::LocalEnv;
use rustc_middle::mir;
use rustc_mir::dataflow::{self, impls::MaybeUninitializedPlaces, move_paths::MoveData};

pub struct Checker<'a> {
    tcx: &'a TyCtxt,
    bb_envs: IndexMap<BasicBlock, BBlockEnv>,
    ret_env: BBlockEnv,
}

impl<'a> Checker<'a> {
    pub fn check<'tcx>(task: CheckingTask<'a, 'tcx>, tcx: &'a TyCtxt) {
        let mut env = LocalEnv::new(tcx);

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
                let refiner = task.refiner_for_block(tcx, &mut env.var_gen, bb);
                BBlockEnv::new(&task.body.local_decls, refiner, &mut vars_in_scope)
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
        for (bb, bb_data) in &task.body.basic_blocks {
            checker.check_basic_block(bb, bb_data, &mut env);
        }

        env.bindings.foo(&mut Fixpoint::default());
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
        let tcx = self.tcx;
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
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
                    let constant = tcx.mk_const(Constant::new(bits, *switch_ty));
                    let guard = tcx.mk_bin_op(BinOp::Eq(*switch_ty), discr.clone(), constant);
                    env.with_guard(guard, |env| {
                        self.check_goto(&self.bb_envs[target], env);
                    });
                }
            }
            TerminatorKind::Return => {
                self.check_goto(&self.ret_env, env);
            }
            TerminatorKind::Call { .. } | TerminatorKind::Assert { .. } => todo!(),
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
                let ret_ty = match bin_op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        assert!(ty1.is_int() && ty2.is_int());
                        BaseTy::Int
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Lte | BinOp::Gte => {
                        assert!(ty1.is_int() && ty2.is_int());
                        BaseTy::Bool
                    }
                    // FIXME: we should check that the operation and operands have the same base type
                    BinOp::Eq(_) | BinOp::Neq(_) => BaseTy::Bool,
                    // Rust's MIR does not have boolean binary operators. They are here just to be
                    // reused in predicates.
                    BinOp::And | BinOp::Or => unreachable!(),
                };
                let pred = tcx.mk_bin_op(
                    BinOp::Eq(ret_ty),
                    tcx.preds.nu(),
                    tcx.mk_bin_op(*bin_op, op1, op2),
                );
                tcx.mk_refine(ret_ty, pred)
            }
            Rvalue::UnaryOp(un_op, op) => {
                let (op, ty) = self.check_operand(op, env);
                let ret_ty = match un_op {
                    UnOp::Not => {
                        assert!(ty.is_bool());
                        BaseTy::Bool
                    }
                    UnOp::Neg => {
                        assert!(ty.is_int());
                        BaseTy::Int
                    }
                };
                let pred =
                    tcx.mk_bin_op(BinOp::Eq(ret_ty), tcx.preds.nu(), tcx.mk_un_op(*un_op, op));
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
                let refine = tcx.mk_bin_op(BinOp::Eq(c.ty()), tcx.preds.nu(), tcx.mk_const(c));
                (tcx.mk_const(c), tcx.mk_refine(c.ty(), refine))
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
        var_gen: &'b mut IndexGen,
        bb: mir::BasicBlock,
    ) -> Refiner {
        Refiner::new(
            tcx,
            &self.move_data,
            self.flow_uninit.entry_set_for_block(bb),
            var_gen,
        )
    }
}
