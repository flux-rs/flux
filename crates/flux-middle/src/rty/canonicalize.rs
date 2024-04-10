//! A canonical type is a type where all [existentials] and [constraint predicates] are *hoisted* to
//! the top level. For example, the canonical version of `(∃a. i32[a], ∃b. { i32[b] | b > 0})` is
//! `∃a,b. { (i32[a], i32[b]) | b > 0}`.
//!
//! Canonicalization can be *shallow* or *deep*, by this we mean that some type constructors
//! introduce new "scopes" that limit the hoisting. For instance, we are not allowed (in general) to
//! hoist an existential type out of a generic argument, for example, in `Vec<∃v. i32[v]>` the
//! existential inside the `Vec` cannot be hoisted out. However, the type inside the generic argument
//! can be canonizalized locally inside the scope of the generic argument. Shallow canonicalization
//! stops when finding type constructors. In contrast, deep canonicalization also canonizalizes inside
//! type constructors. Note that some type constructors like shared references or boxes are transparent
//! to hoisting and do not introduce a new scope.
//!
//! It's also important to note that canonizalization doesn't imply any form of semantic equality
//! and it is just a best effort to facilitate syntactic manipulation. For example, the types
//! `∃a,b. (i32[a], i32[b])` and `∃a,b. (i32[b], i32[a])` are semantically equal but both are in
//! canonical form (in the current implementation).
//!
//! [existentials]: TyKind::Exists
//! [constraint predicates]: TyKind::Constr
use rustc_ast::Mutability;
use rustc_type_ir::INNERMOST;

use super::{
    box_args,
    fold::{TypeFoldable, TypeFolder},
    BaseTy, Binder, BoundVariableKind, Expr, GenericArg, SubsetTy, SubsetTyCtor, Ty, TyKind,
};
use crate::intern::List;

#[derive(Default)]
pub struct ShallowHoister {
    vars: Vec<BoundVariableKind>,
    preds: Vec<Expr>,
}

impl ShallowHoister {
    pub fn into_parts(self) -> (List<BoundVariableKind>, Vec<Expr>) {
        (List::from_vec(self.vars), self.preds)
    }

    pub fn hoist(&mut self, ty: &Ty) -> Ty {
        ty.fold_with(self)
    }
}

impl TypeFolder for ShallowHoister {
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
        let mut hoister = ShallowHoister::default();
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
    /// Guranteed to not have any (shallow) [existential] or [constraint] types
    ///
    /// [existential]: TyKind::Exists
    /// [constraint]: TyKind::Constr
    ty: Ty,
    pred: Expr,
}

impl CanonicalConstrTy {
    pub fn ty(&self) -> Ty {
        self.ty.clone()
    }

    pub fn pred(&self) -> Expr {
        self.pred.clone()
    }
}

/// A (shallowly) canonicalized type. This can be either of the form `{T | p}` or `∃v0,…,vn. {T | p}`,
/// where `T` doesnt have any (shallow) [existential] or [constraint] types.
///
/// When canonizalizing a type without a [constraint] type, `p` will be [`Expr::tt()`].
///
/// [existential]: TyKind::Exists
/// [constraint]: TyKind::Constr
pub enum CanonicalTy {
    /// A type of the form `{T | p}`
    Constr(CanonicalConstrTy),
    /// A type of the form `∃v0,…,vn. {T | p}`
    Exists(Binder<CanonicalConstrTy>),
}

impl CanonicalTy {
    pub fn to_subset_ty_ctor(&self) -> Option<SubsetTyCtor> {
        match self {
            CanonicalTy::Constr(constr) => {
                if let TyKind::Indexed(bty, idx) = constr.ty.kind() {
                    // given {b[e] | p} return λv. {b[v] | p ∧ v == e}
                    let sort = bty.sort();
                    let constr = SubsetTy::new(
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
                        .map(|constr| SubsetTy::new(bty.clone(), Expr::nu(), &constr.pred));
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

    impl_debug_with_default_cx!(CanonicalTy, CanonicalConstrTy);
}
