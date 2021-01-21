use std::collections::HashMap;

use crate::{
    constraint::Constraint,
    env::{OwnershipError, RefKind},
    subtyping::{infer_subst, subtyping},
};
use ast::{FnBody, StatementKind};
use liquid_rust_core::{
    ast::{self, ContDef, FnDef, Rvalue, Statement},
    names::ContId,
    ty::{self, BaseTy, ContTy, Pred, Ty, TyCtxt},
};
use ty::pred;

use crate::env::Env;

pub struct RefineChecker<'a> {
    conts: &'a HashMap<ContId, ContTy>,
    tcx: &'a TyCtxt,
    errors: Vec<OwnershipError>,
}

impl<'a> RefineChecker<'a> {
    pub fn new(tcx: &'a TyCtxt, conts: &'a HashMap<ContId, ContTy>) -> Self {
        Self {
            tcx,
            conts,
            errors: vec![],
        }
    }

    pub fn check_fn_def<I>(
        mut self,
        func: &FnDef<I>,
        fn_ty: &ty::FnTy,
    ) -> Result<Constraint, Vec<OwnershipError>> {
        let mut env = Env::new(self.tcx);
        env.insert_locals(fn_ty.locals(&func.params));
        env.extend_heap(&fn_ty.in_heap);

        let constraint = self.check_body(&mut env, &func.body);

        if self.errors.is_empty() {
            Ok(Constraint::from_bindings(
                fn_ty.in_heap.bindings(),
                constraint,
            ))
        } else {
            Err(self.errors)
        }
    }

    pub fn check_body<I>(&mut self, env: &mut Env, body: &FnBody<I>) -> Constraint {
        match body {
            FnBody::LetCont(defs, rest) => {
                let mut vec = Vec::new();
                for def in defs {
                    vec.push(self.check_cont_def(env, def));
                }
                vec.push(self.check_body(env, rest));
                Constraint::Conj(vec)
            }
            FnBody::Ite { discr, then, else_ } => {
                let snapshot = env.snapshot();
                let c1 = self.check_body(env, then);
                env.rollback_to(snapshot);
                let c2 = self.check_body(env, else_);

                let discr = self.tcx.mk_pred_place(env.resolve_place(discr));
                Constraint::Conj(vec![
                    Constraint::guard(&discr, c1),
                    Constraint::guard(&self.tcx.mk_un_op(ty::UnOp::Not, discr), c2),
                ])
            }
            FnBody::Call { .. } => todo!(),
            FnBody::Jump { target, args } => {
                let cont_ty = &self.conts[target];

                let heap1 = env.heap();
                let locals1 = env.locals();
                let heap2 = &cont_ty.heap;
                let locals2 = &cont_ty.locals(args);

                let subst = infer_subst(heap1, locals1, heap2, locals2);
                let heap2 = &subst.apply(self.tcx, heap2);
                let locals2 = subst.apply(self.tcx, locals2);

                Constraint::Conj(
                    locals2
                        .into_iter()
                        .map(|(x, l)| {
                            let ty1 = &self
                                .tcx
                                .selfify(&env.lookup(&ast::Place::from(x)), pred::Place::from(l));
                            let ty2 = &heap2[&l];
                            subtyping(self.tcx, heap1, ty1, heap2, ty2)
                        })
                        .collect(),
                )
            }
            FnBody::Seq(stmnt, rest) => {
                let (c, bindings) = env.capture_bindings(|env| self.check_stmnt(env, stmnt));
                Constraint::Conj(vec![
                    Constraint::from_bindings(bindings, self.check_body(env, rest)),
                    c,
                ])
            }
            FnBody::Abort => Constraint::True,
        }
    }

    fn check_cont_def<I>(&mut self, env: &mut Env, def: &ContDef<I>) -> Constraint {
        let snapshot = env.snapshot_without_locals();

        let cont_ty = &self.conts[&def.name];
        let bindings = cont_ty.heap.bindings();
        env.insert_locals(cont_ty.locals(&def.params));
        env.extend_heap(&cont_ty.heap);
        let c = self.check_body(env, &def.body);

        env.rollback_to(snapshot);
        Constraint::from_bindings(bindings, c)
    }

    fn check_stmnt<I>(&mut self, env: &mut Env, stmnt: &Statement<I>) -> Constraint {
        match &stmnt.kind {
            StatementKind::Let(x, layout) => {
                env.alloc(*x, self.tcx.mk_ty_for_layout(layout));
                Constraint::True
            }
            StatementKind::Assign(place, rvalue) => {
                let ty = self.check_rvalue(rvalue, env);
                self.check_ownership_safety(RefKind::Mut, place, env);
                env.update(place, ty);
                Constraint::True
            }
            StatementKind::Drop(place) => {
                self.check_ownership_safety(RefKind::Owned, place, env);
                env.drop(place)
            }
            StatementKind::Nop => Constraint::True,
        }
    }

    fn check_rvalue(&mut self, rvalue: &Rvalue, env: &mut Env) -> Ty {
        let tcx = self.tcx;
        match rvalue {
            ast::Rvalue::Use(op) => {
                let pred = self.check_operand(op, env);
                match op {
                    ast::Operand::Use(place) => {
                        let ty = env.lookup(place);
                        self.tcx.selfify(ty, env.resolve_place(place))
                    }
                    ast::Operand::Constant(c) => self.tcx.mk_refine(
                        c.base_ty(),
                        self.tcx.mk_bin_op(ty::BinOp::Eq, tcx.preds.nu(), pred),
                    ),
                }
            }
            ast::Rvalue::Ref(bk, place) => {
                self.check_ownership_safety(RefKind::from(*bk), place, env);
                let l = env.borrow(place);
                self.tcx.mk_ref(*bk, ty::Region::from(place.clone()), l)
            }
            ast::Rvalue::BinaryOp(bin_op, op1, op2) => self.check_bin_op(*bin_op, op1, op2, env),
            ast::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                let ty = self.check_bin_op(*bin_op, op1, op2, env);
                let f1 = tcx.fresh_field();
                let f2 = tcx.fresh_field();
                tcx.mk_tuple(tup!(f1 => ty, f2 => tcx.types.bool()))
            }
            ast::Rvalue::UnaryOp(un_op, op) => match un_op {
                ast::UnOp::Not => {
                    let pred = self.check_operand(op, env);
                    tcx.mk_refine(BaseTy::Bool, pred)
                }
            },
        }
    }

    fn check_bin_op(
        &mut self,
        bin_op: ast::BinOp,
        op1: &ast::Operand,
        op2: &ast::Operand,
        env: &mut Env,
    ) -> Ty {
        use ast::BinOp as ast;
        use ty::BinOp::*;
        let tcx = self.tcx;
        let op1 = self.check_operand(op1, env);
        let op2 = self.check_operand(op2, env);
        let (bty, pred) = match bin_op {
            ast::Add => (
                BaseTy::Int,
                tcx.mk_bin_op(Eq, tcx.preds.nu(), tcx.mk_bin_op(Add, op1, op2)),
            ),
            ast::Sub => (
                BaseTy::Int,
                tcx.mk_bin_op(Eq, tcx.preds.nu(), tcx.mk_bin_op(Sub, op1, op2)),
            ),
            ast::Eq => (
                BaseTy::Bool,
                tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Eq, op1, op2)),
            ),
            ast::Lt => (
                BaseTy::Bool,
                tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Lt, op1, op2)),
            ),
            ast::Le => (
                BaseTy::Bool,
                tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Le, op1, op2)),
            ),
            ast::Ge => (
                BaseTy::Bool,
                tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Ge, op1, op2)),
            ),
            ast::Gt => (
                BaseTy::Bool,
                tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Gt, op1, op2)),
            ),
        };
        tcx.mk_refine(bty, pred)
    }

    fn check_operand(&mut self, operand: &ast::Operand, env: &mut Env) -> Pred {
        match operand {
            ast::Operand::Use(place) => {
                let ty = env.lookup(place);
                if !ty.is_copy() {
                    self.check_ownership_safety(RefKind::Owned, place, env);
                    env.drop(place);
                }
                self.tcx.mk_pred_place(env.resolve_place(place))
            }
            ast::Operand::Constant(c) => {
                let c = match *c {
                    ast::Constant::Bool(b) => pred::Constant::Bool(b),
                    ast::Constant::Int(n) => pred::Constant::Int(n),
                    ast::Constant::Unit => pred::Constant::Unit,
                };
                self.tcx.mk_constant(c)
            }
        }
    }

    // Ownership

    fn check_ownership_safety(&mut self, kind: RefKind, place: &ast::Place, env: &Env) {
        if let Err(err) = env.check_ownership_safety(kind, place, &mut vec![]) {
            self.report_ownership_error(err);
        }
    }

    fn report_ownership_error(&mut self, err: OwnershipError) {
        self.errors.push(err);
    }
}
