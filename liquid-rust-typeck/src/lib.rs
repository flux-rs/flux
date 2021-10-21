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
pub mod subst;
pub mod ty;

use global_env::GlobalEnv;
use liquid_rust_common::index::{Idx, IndexGen};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Constant, Operand, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    ty::{self as core, Name},
};
use liquid_rust_fixpoint::Fixpoint;
use local_env::LocalEnv;
use rustc_hash::FxHashMap;
use rustc_middle::mir::RETURN_PLACE;
use ty::{context::LrCtxt, BinOp, Expr, Sort, Ty, Var};

use crate::{constraint_builder::ConstraintBuilder, lowering::LowerCtxt, subst::Subst, ty::TyKind};

pub struct Checker<'a> {
    lr: &'a LrCtxt,
    body: &'a Body,
    ret_ty: Ty,
    global_env: &'a GlobalEnv,
    constraint: ConstraintBuilder,
    name_gen: IndexGen<Var>,
}

impl Checker<'_> {
    pub fn check(global_env: &GlobalEnv, body: &Body, fn_sig: &core::FnSig) {
        let lr = &LrCtxt::new();
        let mut constraint = ConstraintBuilder::new();

        let name_gen = IndexGen::new();
        let (params, args, ret_ty) = LowerCtxt::lower_with_fresh_names(lr, &name_gen, fn_sig);

        let mut env = LocalEnv::new();

        for (var, sort, pred) in params {
            constraint.push_forall(var, sort, pred);
        }

        for (local, ty) in body.args_iter().zip(args) {
            env.insert_local(local, ty);
        }

        let mut checker = Checker {
            lr,
            global_env,
            body,
            ret_ty,
            constraint: ConstraintBuilder::new(),
            name_gen,
        };

        checker.check_basic_block(BasicBlock::new(0), &mut env);
        println!("{:?}", checker.constraint);
        let constraint = checker.constraint.finalize();
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
                let ret_place_ty = env.lookup_local(RETURN_PLACE);
                self.check_subtyping(ret_place_ty, self.ret_ty.clone());
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);

                let subst = infer_subst(
                    args.iter().map(|op| self.check_operand(op, env)),
                    fn_sig.args.iter(),
                );

                let (params, formals, ret) = LowerCtxt::lower_with_subst(self.lr, &subst, &fn_sig);
                for pred in params {
                    self.constraint.push_head(pred);
                }
                for (op, formal) in args.iter().zip(formals) {
                    let actual = self.check_operand(op, env);
                    self.check_subtyping(actual, formal);
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
            // TODO: we should uninitialize when moving
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
            (ty::TyKind::Int(e1, int_ty1), ty::TyKind::Int(e2, int_ty2)) if int_ty1 == int_ty2 => {
                lr.mk_int(
                    lr.mk_bin_op(ty::BinOp::Add, e1.clone(), e2.clone()),
                    *int_ty1,
                )
            }
            _ => unreachable!("addition between incompatible types"),
        }
    }

    pub fn check_subtyping(&mut self, ty1: Ty, ty2: Ty) {
        let lr = self.lr;
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Int(p1, int_ty1), TyKind::Int(p2, int_ty2)) if int_ty1 == int_ty2 => {
                if p1 != p2 {
                    self.constraint
                        .push_head(lr.mk_bin_op(BinOp::Eq, p1.clone(), p2.clone()));
                }
            }
            (TyKind::ExistsInt(var, int_ty, p), _) => {
                let fresh = self.name_gen.fresh();
                self.constraint.push_forall(
                    fresh,
                    Sort::Int,
                    Subst::new(lr, [(*var, lr.mk_var(fresh))]).subst_expr(p.clone()),
                );
                self.check_subtyping(lr.mk_ty(TyKind::Int(lr.mk_var(fresh), *int_ty)), ty2)
            }
            (TyKind::Int(p1, int_ty1), TyKind::ExistsInt(var, int_ty2, p2))
                if int_ty1 == int_ty2 =>
            {
                self.constraint
                    .push_head(Subst::new(lr, [(*var, p1.clone())]).subst_expr(p2.clone()))
            }
            _ => panic!(
                "unimplemented or subtyping between incompatible types: {:?} {:?}",
                ty1, ty2
            ),
        }
    }
}

fn infer_subst<'a>(
    actuals: impl ExactSizeIterator<Item = Ty>,
    formals: impl ExactSizeIterator<Item = &'a core::Ty>,
) -> FxHashMap<Name, Expr> {
    assert!(actuals.len() == formals.len());

    let mut subst = FxHashMap::default();
    for (actual, formal) in actuals.zip(formals) {
        match (actual.kind(), formal) {
            (TyKind::Int(e1, int_ty1), core::Ty::Int(core::Refine::Var(ident), int_ty2))
                if int_ty1 == int_ty2 =>
            {
                subst.insert(ident.name, e1.clone());
            }
            (TyKind::Int(_, int_ty1), core::Ty::Int(core::Refine::Literal(_), int_ty2))
                if int_ty1 == int_ty2 => {}
            (TyKind::ExistsInt(_, _, _), core::Ty::Int(_, _)) => {
                panic!("unimplemented")
            }
            _ => {
                unreachable!("inferring substitution between incompatible types")
            }
        }
    }
    subst
}
