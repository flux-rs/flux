use std::collections::HashMap;

use crate::{
    constraint::Constraint,
    env::{OwnershipError, RefKind},
};
use ast::{FnBody, StatementKind};
use liquid_rust_core::{
    ast::{self, ContDef, FnDef, Rvalue, Statement},
    names::{ContId, Field},
    ty::{
        self, pred, subst::Subst, BaseTy, ContTy, Heap, LocalsMap, Pred, Ty, TyCtxt, TyKind, TyS,
    },
};
use pred::Place;

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
                            env.subtyping(ty1, heap2, ty2)
                        })
                        .collect(),
                )
            }
            FnBody::Seq(stmnt, rest) => {
                let (c, bindings) = env.capture_bindings(|env| self.check_stmnt(env, stmnt));
                // if !matches!(&stmnt.kind, StatementKind::Nop) {
                //     println!("{}", stmnt);
                //     println!("{}", env.heap());
                //     println!("{}\n", env.locals());
                // }
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
                let (_, ty) = self.check_operand(op, env);
                ty
            }
            ast::Rvalue::Ref(bk, place) => {
                self.check_ownership_safety(RefKind::from(*bk), place, env);
                let l = env.borrow(place);
                self.tcx.mk_ref(*bk, ty::Region::from(place.clone()), l)
            }
            ast::Rvalue::BinaryOp(bin_op, op1, op2) => self.check_bin_op(*bin_op, op1, op2, env),
            ast::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                let ty = self.check_bin_op(*bin_op, op1, op2, env);
                let f1 = tcx.fresh::<Field>();
                let f2 = tcx.fresh::<Field>();
                tcx.mk_tuple(tup!(f1 => ty, f2 => tcx.types.bool()))
            }
            ast::Rvalue::UnaryOp(un_op, op) => self.check_un_op(*un_op, op, env),
        }
    }

    fn check_un_op(&mut self, un_op: ast::UnOp, op: &ast::Operand, env: &mut Env) -> Ty {
        use ty::{BinOp::*, UnOp::*};
        let tcx = self.tcx;
        let (pred, _) = self.check_operand(op, env);
        let pred = match un_op {
            ast::UnOp::Not => tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_un_op(Not, pred)),
        };
        tcx.mk_refine(BaseTy::Bool, pred)
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
        let (op1, _) = self.check_operand(op1, env);
        let (op2, _) = self.check_operand(op2, env);
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

    fn check_operand(&mut self, operand: &ast::Operand, env: &mut Env) -> (Pred, Ty) {
        let tcx = self.tcx;
        match operand {
            ast::Operand::Copy(place) => {
                let ty = tcx.selfify(env.lookup(place), env.resolve_place(place));
                assert!(ty.is_copy());
                (tcx.mk_pred_place(env.resolve_place(place)), ty)
            }
            ast::Operand::Move(place) => {
                let ty = tcx.selfify(env.lookup(place), env.resolve_place(place));
                self.check_ownership_safety(RefKind::Owned, place, env);
                let pred = tcx.mk_pred_place(env.resolve_place(place));
                env.drop(place);
                (pred, ty)
            }
            ast::Operand::Constant(c) => {
                let (bty, c) = match *c {
                    ast::Constant::Bool(b) => (BaseTy::Bool, pred::Constant::Bool(b)),
                    ast::Constant::Int(n) => (BaseTy::Int, pred::Constant::Int(n)),
                    ast::Constant::Unit => (BaseTy::Unit, pred::Constant::Unit),
                };
                let refine =
                    tcx.mk_bin_op(ty::BinOp::Eq, self.tcx.preds.nu(), self.tcx.mk_constant(c));
                (tcx.mk_constant(c), tcx.mk_refine(bty, refine))
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

pub fn subtyping(tcx: &TyCtxt, heap1: &Heap, ty1: &TyS, heap2: &Heap, ty2: &TyS) -> Constraint {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Fn(..), TyKind::Fn(..)) => todo!(),
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => tup1
            .iter()
            .zip(tup2.types())
            .rev()
            .fold(Constraint::True, |c, ((f, ty1), ty2)| {
                Constraint::Conj(vec![
                    subtyping(tcx, heap1, ty1, heap2, ty2),
                    Constraint::from_binding(*f, ty1.clone(), c),
                ])
            }),
        // TODO check regions
        (TyKind::Ref(bk1, _, l1), TyKind::Ref(bk2, _, l2)) if bk1 >= bk2 => {
            let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
            let ty2 = &heap2[l2];
            subtyping(tcx, heap1, ty1, heap2, ty2)
        }
        (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
            let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
            let ty2 = &heap2[l2];
            subtyping(tcx, heap1, ty1, heap2, ty2)
        }
        (TyKind::Refine(bty1, refine1), TyKind::Refine(bty2, refine2)) if bty1 == bty2 => {
            Constraint::from_subtype(*bty1, refine1, refine2)
        }
        (_, TyKind::Uninit(n)) if ty1.size() == *n => Constraint::True,
        _ => bug!("{} {}", ty1, ty2),
    }
}

pub fn infer_subst(heap1: &Heap, locals1: &LocalsMap, heap2: &Heap, locals2: &LocalsMap) -> Subst {
    let mut subst = Subst::new();
    for (x, l2) in locals2 {
        let l1 = &locals1[x];
        let ty1 = &heap1[l1];
        let ty2 = &heap2[l2];
        subst.add_location_subst(*l2, *l1);
        infer_subst_ty(&mut subst, heap1, ty1, heap2, ty2);
    }
    subst
}

fn infer_subst_ty(subst: &mut Subst, heap1: &Heap, ty1: &Ty, heap2: &Heap, ty2: &Ty) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Ref(.., l1), TyKind::Ref(.., l2)) | (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
            subst.add_location_subst(*l2, *l1);
            infer_subst_ty(subst, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
            for ((fld1, ty1), (fld2, ty2)) in tup1.iter().zip(tup2) {
                subst.add_field_subst(*fld2, *fld1);
                infer_subst_ty(subst, heap1, ty1, heap2, ty2);
            }
        }
        _ => {}
    }
}
