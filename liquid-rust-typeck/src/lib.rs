#![feature(rustc_private)]
#![feature(min_specialization)]

extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;

mod constraint_builder;
pub mod global_env;
mod local_env;
mod lowering;
pub mod ty;
mod unification;

use global_env::GlobalEnv;
use liquid_rust_common::index::{Idx, IndexGen};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Operand, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    ty as core,
};
use liquid_rust_fixpoint::Fixpoint;
use local_env::LocalEnv;
use rustc_middle::mir::RETURN_PLACE;
use ty::{context::LrCtxt, EVar, Ty, Var};
use unification::UnificationCtxt;

use crate::lowering::LowerCtxt;

pub struct Checker<'a> {
    lr: &'a LrCtxt,
    body: &'a Body,
    ret_ty: Ty,
    global_env: &'a GlobalEnv,
    name_gen: &'a IndexGen<Var>,
    evar_gen: &'a IndexGen<EVar>,
    unification_cx: &'a mut UnificationCtxt,
}

impl Checker<'_> {
    pub fn check(global_env: &GlobalEnv, body: &Body, fn_sig: &core::FnSig) {
        let lr = &LrCtxt::new();

        let name_gen = &IndexGen::new();
        let (params, args, ret_ty) = LowerCtxt::lower_with_fresh_names(lr, name_gen, fn_sig);

        let mut env = LocalEnv::new(lr, &name_gen);

        for (var, sort, pred) in params {
            env.push_param(var, sort, pred);
        }

        for (local, ty) in body.args_iter().zip(args) {
            env.insert_local(local, ty);
        }

        let mut checker = Checker {
            lr,
            global_env,
            body,
            ret_ty,
            name_gen,
            evar_gen: &IndexGen::new(),
            unification_cx: &mut UnificationCtxt::new(),
        };

        checker.check_basic_block(BasicBlock::new(0), &mut env);
        println!("{:?}", env.constraint);
        println!("{:?}", checker.unification_cx);
        let constraint = env.constraint.finalize(checker.unification_cx);
        println!("{:?}", Fixpoint::check(&constraint));
    }

    fn check_basic_block(&mut self, bb: BasicBlock, env: &mut LocalEnv) {
        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(stmt, env);
        }
        if let Some(terminator) = &data.terminator {
            self.check_terminator(terminator, env);
        }
    }

    fn check_statement(&self, stmt: &Statement, env: &mut LocalEnv) {
        match &stmt.kind {
            StatementKind::Assign(local, rvalue) => {
                let ty = self.check_rvalue(rvalue, env);
                env.insert_local(*local, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(&mut self, terminator: &Terminator, env: &mut LocalEnv) {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = &env.lookup_local(RETURN_PLACE);
                env.check_subtyping(self.unification_cx, ret_place_ty, &self.ret_ty);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);
                let (params, formals, ret) =
                    LowerCtxt::lower_with_fresh_evars(self.lr, self.unification_cx, &fn_sig);
                for (_, _, pred) in params {
                    env.constraint.push_head(pred);
                }
                for (op, formal) in args.iter().zip(formals) {
                    let actual = self.check_operand(op, env);
                    env.check_subtyping(&mut self.unification_cx, &actual, &formal);
                }
                if let Some((local, bb)) = destination {
                    env.insert_local(*local, ret);
                    self.check_basic_block(*bb, env);
                }
            }
        }
    }

    fn check_rvalue(&self, rvalue: &Rvalue, env: &mut LocalEnv) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(operand, env),
            Rvalue::BinaryOp(bin_op, op1, op2) => self.check_binary_op(bin_op, op1, op2, env),
        }
    }

    fn check_operand(&self, operand: &Operand, env: &mut LocalEnv) -> Ty {
        match operand {
            // TODO: should we do something different for move?
            Operand::Copy(local) | Operand::Move(local) => env.lookup_local(*local),
            Operand::Constant(c) => self.check_constant(c),
        }
    }

    fn check_constant(&self, c: &Constant) -> Ty {
        let lr = self.lr;
        match c {
            Constant::Int(n, int_ty) => {
                let expr = lr.mk_constant(ty::Constant::from(*n));
                lr.mk_int(expr, *int_ty)
            }
            Constant::Uint(n, int_ty) => {
                let expr = lr.mk_constant(ty::Constant::from(*n));
                lr.mk_uint(expr, *int_ty)
            }
        }
    }

    fn check_binary_op(
        &self,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
        env: &mut LocalEnv,
    ) -> Ty {
        match bin_op {
            ir::BinOp::Add => self.check_add(op1, op2, env),
        }
    }

    fn check_add(&self, op1: &Operand, op2: &Operand, env: &mut LocalEnv) -> Ty {
        let lr = self.lr;
        let ty1 = self.check_operand(op1, env);
        let ty2 = self.check_operand(op2, env);
        match (ty1.kind(), ty2.kind()) {
            (ty::TyKind::Int(refine1, int_ty1), ty::TyKind::Int(refine2, int_ty2))
                if int_ty1 == int_ty2 =>
            {
                let e1 = refine1.to_expr(self.lr);
                let e2 = refine2.to_expr(self.lr);
                lr.mk_int(lr.mk_bin_op(ty::BinOp::Add, e1, e2), *int_ty1)
            }
            (ty::TyKind::Uint(refine1, int_ty1), ty::TyKind::Uint(refine2, int_ty2))
                if int_ty1 == int_ty2 =>
            {
                let e1 = refine1.to_expr(self.lr);
                let e2 = refine2.to_expr(self.lr);
                lr.mk_uint(lr.mk_bin_op(ty::BinOp::Add, e1, e2), *int_ty1)
            }
            _ => unreachable!("addition between incompatible types"),
        }
    }
}

// foo: forall n: int. (n + 1) @ i32 -> (n + 2) @ i32
//
// foo<m>(m)
// m: int { m = 1 }
