#![feature(rustc_private)]
#![feature(min_specialization)]

extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

mod constraint_builder;
pub mod global_env;
mod local_env;
mod lowering;
pub mod subst;
pub mod ty;

use crate::{
    constraint_builder::{ConstraintBuilder, Cursor},
    lowering::LowerCtxt,
    subst::Subst,
    ty::TyKind,
};
use global_env::GlobalEnv;
use liquid_rust_common::{
    errors::ErrorReported,
    index::{Idx, IndexGen},
};
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
use rustc_middle::mir::{SourceInfo, RETURN_PLACE};
use rustc_session::Session;
use rustc_span::MultiSpan;
use ty::{context::LrCtxt, BaseTy, BinOp, Expr, Sort, Ty, Var};

pub struct Checker<'a> {
    lr: &'a LrCtxt,
    sess: &'a Session,
    body: &'a Body,
    ret_ty: Ty,
    global_env: &'a GlobalEnv,
    name_gen: IndexGen<Var>,
}

impl Checker<'_> {
    pub fn check(
        global_env: &GlobalEnv,
        sess: &Session,
        body: &Body,
        fn_sig: &core::FnSig,
    ) -> Result<(), ErrorReported> {
        let lr = &LrCtxt::new();
        let mut constraint = ConstraintBuilder::new();

        let name_gen = IndexGen::new();
        let (params, args, ret_ty) = LowerCtxt::lower_with_fresh_names(lr, &name_gen, fn_sig);

        let mut env = LocalEnv::new();

        let mut cursor = constraint.as_cursor();
        for (var, sort, pred) in params {
            cursor.push_forall(var, sort, pred);
        }

        for (local, ty) in body.args_iter().zip(args) {
            env.insert_local(local, ty);
        }

        let checker = Checker {
            lr,
            sess,
            global_env,
            body,
            ret_ty,
            name_gen,
        };

        checker.check_basic_block(&mut env, &mut cursor, BasicBlock::new(0))?;
        println!("{:?}", constraint);
        let constraint = constraint.finalize();
        println!("{:?}", Fixpoint::check(&constraint));
        Ok(())
    }

    fn check_basic_block(
        &self,
        env: &mut LocalEnv,
        cursor: &mut Cursor,
        bb: BasicBlock,
    ) -> Result<(), ErrorReported> {
        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.check_statement(env, cursor, stmt);
        }
        if let Some(terminator) = &data.terminator {
            self.check_terminator(env, cursor, terminator)?;
        }
        Ok(())
    }

    fn check_statement(&self, env: &mut LocalEnv, cursor: &mut Cursor, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(local, rvalue) => {
                let ty = self.check_rvalue(env, cursor, rvalue);
                env.insert_local(*local, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(
        &self,
        env: &mut LocalEnv,
        cursor: &mut Cursor,
        terminator: &Terminator,
    ) -> Result<(), ErrorReported> {
        match &terminator.kind {
            TerminatorKind::Return => {
                let ret_place_ty = env.lookup_local(RETURN_PLACE);
                self.check_subtyping(cursor, ret_place_ty, self.ret_ty.clone());
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);

                let subst = self.infer_subst(
                    cursor,
                    args.iter().map(|op| self.check_operand(env, op)),
                    fn_sig.args.iter(),
                );
                self.check_subst(&subst, &fn_sig.params, terminator.source_info)?;

                let (params, formals, ret) =
                    LowerCtxt::lower_with_subst(self.lr, &self.name_gen, subst, &fn_sig);
                for pred in params {
                    cursor.push_head(pred);
                }
                for (op, formal) in args.iter().zip(formals) {
                    let actual = self.check_operand(env, op);
                    self.check_subtyping(&mut cursor.snapshot(), actual, formal);
                }
                if let Some((local, bb)) = destination {
                    env.insert_local(*local, ret);
                    self.check_basic_block(env, cursor, *bb)?;
                }
            }
        }
        Ok(())
    }

    fn check_rvalue(&self, env: &mut LocalEnv, cursor: &mut Cursor, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(env, cursor, bin_op, op1, op2)
            }
        }
    }

    fn check_operand(&self, env: &mut LocalEnv, operand: &Operand) -> Ty {
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
                lr.mk_refine(BaseTy::Int(*int_ty), expr)
            }
        }
    }

    fn check_binary_op(
        &self,
        env: &mut LocalEnv,
        cursor: &mut Cursor,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        match bin_op {
            ir::BinOp::Add => self.check_add(env, cursor, op1, op2),
        }
    }

    fn check_add(
        &self,
        env: &mut LocalEnv,
        cursor: &mut Cursor,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let lr = self.lr;
        let ty1 = self.unpack(cursor, self.check_operand(env, op1));
        let ty2 = self.unpack(cursor, self.check_operand(env, op2));

        match (ty1.kind(), ty2.kind()) {
            (ty::TyKind::Refine(bty1, e1), ty::TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                lr.mk_refine(*bty1, lr.mk_bin_op(ty::BinOp::Add, e1.clone(), e2.clone()))
            }
            _ => unreachable!("implement existentials"),
        }
    }

    fn unpack(&self, cursor: &mut Cursor, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Refine(_, _) => ty,
            TyKind::Exists(bty, evar, e) => {
                let lr = self.lr;
                let fresh = self.name_gen.fresh();
                cursor.push_forall(
                    fresh,
                    bty.sort(),
                    Subst::new(lr, [(*evar, lr.mk_var(fresh))]).subst_expr(e.clone()),
                );
                lr.mk_refine(*bty, lr.mk_var(fresh))
            }
        }
    }

    fn check_subtyping(&self, cursor: &mut Cursor, ty1: Ty, ty2: Ty) {
        let lr = self.lr;
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                if e1 != e2 {
                    cursor.push_head(lr.mk_bin_op(BinOp::Eq, e1.clone(), e2.clone()));
                }
            }
            (TyKind::Exists(bty, evar, e), _) => {
                let fresh = self.name_gen.fresh();
                cursor.push_forall(
                    fresh,
                    Sort::Int,
                    Subst::new(lr, [(*evar, lr.mk_var(fresh))]).subst_expr(e.clone()),
                );
                self.check_subtyping(
                    cursor,
                    lr.mk_ty(TyKind::Refine(*bty, lr.mk_var(fresh))),
                    ty2,
                )
            }
            (TyKind::Refine(bty1, e1), TyKind::Exists(bty2, evar, e2)) => {
                debug_assert_eq!(bty1, bty2);
                cursor.push_head(Subst::new(lr, [(*evar, e1.clone())]).subst_expr(e2.clone()))
            }
        }
    }

    fn infer_subst<'a>(
        &self,
        cursor: &mut Cursor,
        actuals: impl ExactSizeIterator<Item = Ty>,
        formals: impl ExactSizeIterator<Item = &'a core::Ty>,
    ) -> FxHashMap<Name, Expr> {
        assert!(actuals.len() == formals.len());
        let lr = self.lr;

        let mut subst = FxHashMap::default();
        for (actual, formal) in actuals.zip(formals) {
            let (bty2, ident) = match formal {
                core::Ty::Refine(bty2, core::Refine::Var(ident)) => (bty2, ident),
                core::Ty::Refine(_, core::Refine::Literal(..)) => continue,
                core::Ty::Exists(_, _, _) => continue,
            };

            match actual.kind() {
                TyKind::Refine(bty1, e) => {
                    debug_assert!(bty1 == bty2);
                    subst.insert(ident.name, e.clone());
                }
                TyKind::Exists(bty1, evar, e) => {
                    debug_assert!(bty1 == bty2);
                    let fresh = self.name_gen.fresh();
                    cursor.push_forall(
                        fresh,
                        bty1.sort(),
                        Subst::new(lr, [(*evar, lr.mk_var(fresh))]).subst_expr(e.clone()),
                    );
                    subst.insert(ident.name, lr.mk_var(fresh));
                }
            }
        }
        subst
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
                        "cannot infer the value of pure parameter `{}` for this function call",
                        param.name.symbol
                    ),
                );
                s.push_span_label(param.name.span, "parameter declared here".to_string());
                self.sess.span_err(s, "parameter inference failed");
                return Err(ErrorReported);
            }
        }
        Ok(())
    }
}
