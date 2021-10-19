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

use liquid_rust_common::index::{Idx, IndexGen};
use liquid_rust_core::{
    ir::{
        BasicBlock, Body, Constant, Operand, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    ty as core,
};
use liquid_rust_fixpoint::Fixpoint;
use local_env::LocalEnv;
use rustc_middle::mir::RETURN_PLACE;
use ty::{context::LrCtxt, Ty};

use crate::lowering::LowerCtxt;

pub struct Checker<'a> {
    lr: &'a LrCtxt,
    body: &'a Body,
    ret_ty: &'a Ty,
}

impl Checker<'_> {
    pub fn check(lr: &LrCtxt, body: &Body, fn_sig: &core::FnSig) {
        let name_gen = IndexGen::new();
        let fn_sig = LowerCtxt::lower(lr, &name_gen, fn_sig);

        let mut env = LocalEnv::new(lr, &name_gen);

        for (name, rty) in &fn_sig.params {
            env.push_param(*name, rty.clone());
        }

        for (local, ty) in body.args_iter().zip(&fn_sig.args) {
            env.insert_local(local, ty.clone());
        }

        let checker = Checker {
            lr,
            body,
            ret_ty: &fn_sig.ret,
        };

        checker.check_basic_block(BasicBlock::new(0), &mut env);
        println!("{:?}", Fixpoint::check(&env.into_constraint()));
    }

    fn check_basic_block(&self, bb: BasicBlock, env: &mut LocalEnv) {
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

    fn check_terminator(&self, terminator: &Terminator, env: &mut LocalEnv) {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = &env.lookup_local(RETURN_PLACE);
                env.check_subtyping(ret_place_ty, self.ret_ty);
            }
        }
    }

    fn check_rvalue(&self, rvalue: &Rvalue, env: &mut LocalEnv) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(operand, env),
        }
    }

    fn check_operand(&self, operand: &Operand, env: &mut LocalEnv) -> Ty {
        match operand {
            Operand::Copy(local) => env.lookup_local(*local),
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
}
