use liquid_rust_common::index::IndexGen;
use liquid_rust_core::{
    ir::Local,
    ty::{
        context::LrCtxt,
        pure::{BinOp, RType, Var},
        Refine, Sort, Ty, TyKind,
    },
};
use liquid_rust_fixpoint::Constraint;
use rustc_hash::FxHashMap;

use crate::constraint_builder::ConstraintBuilder;

pub struct LocalEnv<'tck> {
    lr: &'tck LrCtxt,
    locals: FxHashMap<Local, Ty>,
    pub constraint: ConstraintBuilder,
    name_gen: IndexGen<Var>,
}

impl<'tck> LocalEnv<'tck> {
    pub fn new(lr: &'tck LrCtxt) -> LocalEnv {
        LocalEnv {
            lr,
            locals: FxHashMap::default(),
            constraint: ConstraintBuilder::new(),
            name_gen: IndexGen::new(),
        }
    }

    pub fn to_constraint(self) -> Constraint {
        self.constraint.finalize()
    }

    pub fn fresh_name(&self) -> Var {
        self.name_gen.fresh()
    }

    pub fn push_param(&mut self, x: Var, rty: RType) {
        self.constraint.push_forall(x, rty);
    }

    pub fn insert_local(&mut self, local: Local, ty: Ty) {
        self.locals.insert(local, ty);
    }

    pub fn lookup_local(&mut self, local: Local) -> Ty {
        self.locals.get(&local).cloned().unwrap()
    }

    pub fn check_subtyping(&mut self, ty1: &Ty, ty2: &Ty) {
        let lr = self.lr;
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Int(n1, int_ty1), TyKind::Int(n2, int_ty2)) if int_ty1 == int_ty2 => {
                let fresh = self.fresh_name();
                let var = lr.mk_var(fresh);
                let p1 = lr.mk_bin_op(BinOp::Eq, var.clone(), n1.clone());
                let p2 = lr.mk_bin_op(BinOp::Eq, var, n2.clone());
                self.constraint.push_forall(
                    fresh,
                    RType {
                        sort: Sort::Int,
                        refine: Refine::Pred(p1),
                    },
                );
                self.constraint.push_head(p2);
            }
            (TyKind::Uint(n1, int_ty1), TyKind::Uint(n2, int_ty2)) if int_ty1 == int_ty2 => {
                let fresh = self.fresh_name();
                let var = lr.mk_var(fresh);
                let p1 = lr.mk_bin_op(BinOp::Eq, var.clone(), n1.clone());
                let p2 = lr.mk_bin_op(BinOp::Eq, var, n2.clone());
                self.constraint.push_forall(
                    fresh,
                    RType {
                        sort: Sort::Int,
                        refine: Refine::Pred(p1),
                    },
                );
                self.constraint.push_head(p2);
            }
            _ => unreachable!("Subtyping between incompatible types"),
        }
    }
}
