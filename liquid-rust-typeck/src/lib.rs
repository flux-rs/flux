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
mod lowering;
pub mod subst;
pub mod ty;
mod tyenv;

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
use rustc_hash::FxHashMap;
use rustc_middle::mir::{SourceInfo, RETURN_PLACE};
use rustc_session::Session;
use rustc_span::MultiSpan;
use ty::{context::LrCtxt, BaseTy, BinOp, Expr, Ty, Var};
use tyenv::TyEnv;

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

        let mut env = TyEnv::new();

        let mut cursor = constraint.as_cursor();
        for (var, sort, pred) in params {
            cursor.push_forall(var, sort, pred);
        }

        for (local, ty) in body.args_iter().zip(args) {
            env.insert_local(local, ty);
        }

        for local in body.vars_and_temps_iter() {
            env.insert_local(local, lr.mk_uninit(body.local_decls[local].layout.clone()));
        }

        env.insert_local(
            RETURN_PLACE,
            lr.mk_uninit(body.local_decls[RETURN_PLACE].layout.clone()),
        );

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
        env: &mut TyEnv,
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

    fn check_statement(&self, env: &mut TyEnv, cursor: &mut Cursor, stmt: &Statement) {
        match &stmt.kind {
            // OWNERSHIP CHECK
            StatementKind::Assign(p, rvalue) => {
                let ty = self.check_rvalue(env, cursor, rvalue);
                env.write_place(p, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn check_terminator(
        &self,
        env: &mut TyEnv,
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
                    terminator.source_info,
                    args.iter().map(|op| self.check_operand(env, op)),
                    fn_sig.args.iter(),
                )?;
                self.check_subst(&subst, &fn_sig.params, terminator.source_info)?;

                let (params, formals, ret) =
                    LowerCtxt::lower_with_subst(self.lr, &self.name_gen, subst, fn_sig);
                for pred in params {
                    cursor.push_head(pred);
                }
                for (op, formal) in args.iter().zip(formals) {
                    let actual = self.check_operand(env, op);
                    self.check_subtyping(&mut cursor.snapshot(), actual, formal);
                }
                if let Some((p, bb)) = destination {
                    env.write_place(p, ret);
                    self.check_basic_block(env, cursor, *bb)?;
                }
            }
        }
        Ok(())
    }

    fn check_rvalue(&self, env: &mut TyEnv, cursor: &mut Cursor, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(operand) => self.check_operand(env, operand),
            Rvalue::BinaryOp(bin_op, op1, op2) => {
                self.check_binary_op(env, cursor, bin_op, op1, op2)
            }
            // TODO: this should check ownership safety
            Rvalue::MutRef(local) => self.lr.mk_mut_ref(*local),
        }
    }

    fn check_operand(&self, env: &mut TyEnv, operand: &Operand) -> Ty {
        match operand {
            // OWNERSHIP CHECK
            // TODO: we should uninitialize when moving and also check ownership safety
            Operand::Copy(p) | Operand::Move(p) => env.lookup_place(p),
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
        env: &mut TyEnv,
        cursor: &mut Cursor,
        bin_op: &ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        match bin_op {
            ir::BinOp::Add => self.check_add(env, cursor, op1, op2),
        }
    }

    fn check_add(&self, env: &mut TyEnv, cursor: &mut Cursor, op1: &Operand, op2: &Operand) -> Ty {
        let lr = self.lr;
        let ty1 = self.unpack(cursor, self.check_operand(env, op1));
        let ty2 = self.unpack(cursor, self.check_operand(env, op2));

        match (ty1.kind(), ty2.kind()) {
            (ty::TyKind::Refine(bty1, e1), ty::TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                lr.mk_refine(*bty1, lr.mk_bin_op(ty::BinOp::Add, e1.clone(), e2.clone()))
            }
            _ => unreachable!("addition between incompatible types"),
        }
    }

    fn unpack(&self, cursor: &mut Cursor, ty: Ty) -> Ty {
        match ty.kind() {
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
            TyKind::Refine(_, _) | TyKind::Uninit(_) | TyKind::MutRef(_) => ty,
        }
    }

    fn check_subtyping(&self, cursor: &mut Cursor, ty1: Ty, ty2: Ty) {
        let lr = self.lr;
        let ty1 = self.unpack(cursor, ty1);
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                if e1 != e2 {
                    cursor.push_head(lr.mk_bin_op(BinOp::Eq, e1.clone(), e2.clone()));
                }
            }
            (TyKind::Refine(bty1, e1), TyKind::Exists(bty2, evar, e2)) => {
                debug_assert_eq!(bty1, bty2);
                cursor.push_head(Subst::new(lr, [(*evar, e1.clone())]).subst_expr(e2.clone()))
            }
            (TyKind::MutRef(r1), TyKind::MutRef(r2)) => {
                assert!(r1 == r2);
            }
            (TyKind::Uninit(_), _) | (_, TyKind::Uninit(_)) => {
                unreachable!("subtyping between uninitialized types")
            }
            (TyKind::Exists(..), _) => {
                unreachable!("subtyping with unpacked existential")
            }
            _ => {
                unreachable!("subtyping between incompatible types")
            }
        }
    }

    fn infer_subst<'a>(
        &self,
        cursor: &mut Cursor,
        source_info: SourceInfo,
        actuals: impl ExactSizeIterator<Item = Ty>,
        formals: impl ExactSizeIterator<Item = &'a core::Ty>,
    ) -> Result<FxHashMap<Name, Expr>, ErrorReported> {
        assert!(actuals.len() == formals.len());
        let lr = self.lr;

        let mut subst = FxHashMap::default();
        for (actual, formal) in actuals.zip(formals) {
            let (bty2, ident) = match formal {
                core::Ty::Refine(bty2, core::Refine::Var(ident)) => (bty2, ident),
                core::Ty::Refine(_, _) => continue,
                core::Ty::Exists(_, _, _) => continue,
            };

            match actual.kind() {
                TyKind::Refine(bty1, e) => {
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
                TyKind::Uninit(_) => {
                    unreachable!("inferring substitution with uninitialized type")
                }
                // TODO: we should also infer region substitution
                TyKind::MutRef(_) => {}
            }
        }
        Ok(subst)
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
