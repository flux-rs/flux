use crate::{
    ty::{context::LrCtxt, BinOp, Pred, Refine, Sort, Ty, TyKind, Var},
    unification::UnificationCtxt,
};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ir::Local;
use liquid_rust_fixpoint::Constraint;
use rustc_hash::FxHashMap;

use crate::constraint_builder::ConstraintBuilder;

pub struct LocalEnv<'a> {
    lr: &'a LrCtxt,
    locals: FxHashMap<Local, Ty>,
    pub constraint: ConstraintBuilder,
    name_gen: &'a IndexGen<Var>,
}

impl<'a> LocalEnv<'a> {
    pub fn new(lr: &'a LrCtxt, name_gen: &'a IndexGen<Var>) -> Self {
        LocalEnv {
            lr,
            locals: FxHashMap::default(),
            constraint: ConstraintBuilder::new(),
            name_gen,
        }
    }

    pub fn fresh_name(&self) -> Var {
        self.name_gen.fresh()
    }

    pub fn push_param(&mut self, name: Var, sort: Sort, pred: Pred) {
        self.constraint.push_forall(name, sort, pred);
    }

    pub fn insert_local(&mut self, local: Local, ty: Ty) {
        self.locals.insert(local, ty);
    }

    pub fn lookup_local(&mut self, local: Local) -> Ty {
        self.locals.get(&local).cloned().unwrap()
    }

    pub fn check_subtyping(&mut self, unification_cx: &mut UnificationCtxt, ty1: &Ty, ty2: &Ty) {
        let lr = self.lr;
        match (ty1.kind(), ty2.kind()) {
            (
                TyKind::Int(Refine::EVar(evar1), int_ty1),
                TyKind::Int(Refine::EVar(evar2), int_ty2),
            ) if int_ty1 == int_ty2 => {
                unification_cx.unify(*evar1, *evar2);
            }
            (TyKind::Int(Refine::Expr(p), int_ty1), TyKind::Int(Refine::EVar(evar), int_ty2))
                if int_ty1 == int_ty2 =>
            {
                unification_cx.instantiate(*evar, p.clone(), Sort::Int);
            }
            (TyKind::Int(Refine::Expr(p1), int_ty1), TyKind::Int(Refine::Expr(p2), int_ty2))
                if int_ty1 == int_ty2 =>
            {
                self.constraint
                    .push_head(lr.mk_bin_op(BinOp::Eq, p1.clone(), p2.clone()));
            }
            (TyKind::Int(Refine::EVar(evar), int_ty1), TyKind::Int(Refine::Expr(p2), int_ty2))
                if int_ty1 == int_ty2 =>
            {
                let p1 = lr.mk_evar(*evar);
                self.constraint
                    .push_head(lr.mk_bin_op(BinOp::Eq, p1, p2.clone()));
            }
            (TyKind::Uint(Refine::Expr(p1), int_ty1), TyKind::Uint(Refine::Expr(p2), int_ty2))
                if int_ty1 == int_ty2 =>
            {
                self.constraint
                    .push_head(lr.mk_bin_op(BinOp::Eq, p1.clone(), p2.clone()));
            }
            _ => panic!("unimplemented or subtyping between incompatible types"),
        }
    }
}
