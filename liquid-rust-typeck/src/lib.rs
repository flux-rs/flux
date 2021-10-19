#![feature(rustc_private)]
#![feature(min_specialization)]

extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_serialize;

mod constraint_builder;
pub mod global_env;
mod local_env;

use liquid_rust_common::index::Idx;
use liquid_rust_core::{
    ir::{
        BasicBlock, Body, Constant, Operand, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    ty::{self, context::LrCtxt, subst::Subst, FnSig, Ty},
};
use liquid_rust_fixpoint::Fixpoint;
use local_env::LocalEnv;
use rustc_middle::mir::RETURN_PLACE;

pub struct Checker<'tck> {
    lr: &'tck LrCtxt,
    body: &'tck Body,
    ret_ty: &'tck Ty,
}

impl<'tck> Checker<'tck> {
    pub fn check(lr: &LrCtxt, body: &Body, fn_sig: &FnSig) {
        let mut env = LocalEnv::new(lr);

        let mut subst = Subst::new(lr);
        for (param_name, param_ty) in &fn_sig.params {
            let fresh_name = env.fresh_name();
            env.push_param(fresh_name, subst.subst_rtype(param_ty.clone()));
            subst.insert(*param_name, lr.mk_var(fresh_name));
        }

        for (local, ty) in body.args_iter().zip(&fn_sig.args) {
            env.insert_local(local, subst.subst_ty(ty.clone()));
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
