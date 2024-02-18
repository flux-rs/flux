use rustc_type_ir::{Mutability, INNERMOST};

use super::{
    box_args,
    fold::{TypeFoldable, TypeFolder},
    BaseTy, Binder, BoundVariableKind, Expr, GenericArg, SimpleTy, SimpleTyCtor, Ty, TyKind,
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
            TyKind::Indexed(bty, idx) => Ty::indexed(bty.fold_with(self), idx.clone()),
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
        let constr_ty = CanonicalConstrTy { ty, pred };
        if vars.is_empty() {
            CanonicalTy::Constr(constr_ty)
        } else {
            CanonicalTy::Exists(Binder::new(constr_ty, vars))
        }
    }
}
pub struct CanonicalConstrTy {
    ty: Ty,
    pred: Expr,
}

pub enum CanonicalTy {
    Constr(CanonicalConstrTy),
    Exists(Binder<CanonicalConstrTy>),
}

impl CanonicalTy {
    pub fn to_simple_ty_ctor(&self) -> Option<SimpleTyCtor> {
        match self {
            CanonicalTy::Constr(constr) => {
                if let TyKind::Indexed(bty, idx) = constr.ty.kind() {
                    // given {b[e] | p} return λv. {b[v] | p ∧ v == e}
                    let sort = bty.sort();
                    let constr = SimpleTy::new(
                        bty.clone(),
                        Expr::nu(),
                        Expr::and([constr.pred.clone(), Expr::eq(Expr::nu(), idx)]),
                    );
                    Some(Binder::with_sort(constr, sort))
                } else {
                    None
                }
            }
            CanonicalTy::Exists(poly_constr) => {
                let constr = poly_constr.as_ref().skip_binder();
                if let TyKind::Indexed(bty, idx) = constr.ty.kind()
                    && idx.is_nu()
                {
                    let ctor = poly_constr
                        .as_ref()
                        .map(|constr| SimpleTy::new(bty.clone(), Expr::nu(), &constr.pred));
                    Some(ctor)
                } else {
                    None
                }
            }
        }
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;

    impl Pretty for CanonicalConstrTy {
        fn fmt(&self, cx: &PrettyCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            define_scoped!(cx, f);
            w!("{{ {:?} | {:?} }}", &self.ty, &self.pred)
        }
    }

    impl Pretty for CanonicalTy {
        fn fmt(&self, cx: &PrettyCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            define_scoped!(cx, f);
            match self {
                CanonicalTy::Constr(constr) => w!("{:?}", constr),
                CanonicalTy::Exists(poly_constr) => {
                    cx.with_bound_vars(poly_constr.vars(), || {
                        cx.fmt_bound_vars("∃", poly_constr.vars(), ". ", f)?;
                        w!("{:?}", poly_constr.as_ref().skip_binder())
                    })
                }
            }
        }
    }

    impl_debug_with_default_cx!(CanonicalTy);
}
