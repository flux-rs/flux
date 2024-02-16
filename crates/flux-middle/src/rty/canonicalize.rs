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
                ty.replace_bound_refts_with(|sort, mode, kind| {
                    let idx = self.vars.len();
                    self.vars
                        .push(BoundVariableKind::Refine(sort.clone(), mode, kind));
                    Expr::late_bvar(INNERMOST, idx as u32, kind)
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

impl CanonicalTy {
    pub fn to_bty_arg(&self) -> Option<GenericArg> {
        todo!()
        // match self {
        //     CanonicalTy::Exists(poly_constr_ty) => {
        //         let vars = poly_constr_ty.vars();
        //         let constr_ty = poly_constr_ty.as_ref().skip_binder();
        //         if let TyKind::Indexed(_, idx) = constr_ty.ty.kind()
        //             && idx.is_nu()
        //         {
        //             let ty = constr_ty.to_ty();
        //             Some(GenericArg::Base(Binder::new(ty, vars.clone())))
        //         } else {
        //             None
        //         }
        //     }
        //     CanonicalTy::Constr(constr_ty) => {
        //         if let TyKind::Indexed(bty, idx) = constr_ty.ty.kind() {
        //             let sort = bty.sort();
        //             let infer_mode = sort.default_infer_mode();
        //             let ty = Ty::constr(Expr::eq(Expr::nu(), idx), Ty::indexed(bty.clone(), idx));
        //             let vars = List::singleton(BoundVariableKind::Refine(
        //                 sort,
        //                 infer_mode,
        //                 BoundReftKind::Annon,
        //             ));
        //             Some(GenericArg::Base(Binder::new(ty, vars)))
        //         } else {
        //             None
        //         }
        //     }
        // }
    }
}

pub struct ConstrTy {
    ty: Ty,
    pred: Expr,
}

impl ConstrTy {
    pub fn to_ty(&self) -> Ty {
        if self.pred.is_trivially_true() {
            self.ty.clone()
        } else {
            Ty::constr(self.pred.clone(), self.ty.clone())
        }
    }
}
