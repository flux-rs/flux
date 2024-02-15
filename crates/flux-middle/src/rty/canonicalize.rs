use rustc_type_ir::{Mutability, INNERMOST};

use super::{
    box_args,
    fold::{TypeFoldable, TypeFolder},
    BaseTy, Binder, BoundVariableKind, Expr, GenericArg, Ty, TyKind,
};
use crate::intern::List;

#[derive(Default)]
pub struct Hoister {
    vars: Vec<BoundVariableKind>,
    preds: Vec<Expr>,
}

impl Hoister {
    pub fn into_parts(self) -> (List<BoundVariableKind>, Vec<Expr>) {
        (List::from_vec(self.vars), self.preds)
    }

    pub fn hoist(&mut self, ty: &Ty) -> Ty {
        ty.fold_with(self)
    }
}

impl TypeFolder for Hoister {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(ty) => {
                ty.replace_bound_exprs_with(|sort, mode| {
                    let idx = self.vars.len();
                    self.vars
                        .push(BoundVariableKind::Refine(sort.clone(), mode));
                    Expr::late_bvar(INNERMOST, idx as u32)
                })
                .fold_with(self)
            }
            TyKind::Constr(pred, ty) => {
                self.preds.push(pred.clone());
                ty.fold_with(self)
            }
            _ => ty.clone(),
        }
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, args) if adt_def.is_box() => {
                let (boxed, alloc) = box_args(args);
                let args = List::from_arr([
                    GenericArg::Ty(boxed.fold_with(self)),
                    GenericArg::Ty(alloc.clone()),
                ]);
                BaseTy::Adt(adt_def.clone(), args)
            }
            BaseTy::Ref(re, ty, Mutability::Not) => {
                BaseTy::Ref(*re, ty.fold_with(self), Mutability::Not)
            }
            BaseTy::Tuple(tys) => BaseTy::Tuple(tys.fold_with(self)),
            _ => bty.clone(),
        }
    }
}

impl Ty {
    pub fn shallow_canonicalize(&self) -> CanonicalTy {
        let mut hoister = Hoister::default();
        let ty = hoister.hoist(self);
        let (vars, preds) = hoister.into_parts();
        let pred = Expr::and(preds);
        let constr_ty = ConstrTy { ty, pred };
        if vars.is_empty() {
            CanonicalTy::Constr(constr_ty)
        } else {
            CanonicalTy::Exists(Binder::new(constr_ty, vars))
        }
    }
}

pub enum CanonicalTy {
    Exists(Binder<ConstrTy>),
    Constr(ConstrTy),
}

pub struct ConstrTy {
    ty: Ty,
    pred: Expr,
}
