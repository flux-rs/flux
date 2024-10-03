//! A canonical type is a type where all [existentials] and [constraint predicates] are *hoisted* to
//! the top level. For example, the canonical version of `∃a. {∃b. i32[a + b] | b > 0}` is
//! `∃a,b. {i32[a + b] | b > 0}`.
//!
//! Canonicalization can be *shallow* or *deep*, by this we mean that some type constructors
//! introduce new "scopes" that limit the hoisting. For instance, we are not allowed (in general) to
//! hoist an existential type out of a generic argument, for example, in `Vec<∃v. i32[v]>` the
//! existential inside the `Vec` cannot be hoisted out. However, the type inside the generic argument
//! can be canonizalized locally inside the scope of the generic argument. Shallow canonicalization
//! stops when finding type constructors. In contrast, deep canonicalization also canonicalizes inside
//! type constructors.
//!
//! Note that existentials inside some type constructors like shared references, tuples or boxes can
//! be hoisted soundly, e.g., `(∃a. i32[a], ∃b. i32[b])` is equivalent to `∃a,b. (i32[a], i32[b])`
//! and `&∃a. i32[a]` is equivalent to `∃a. &i32[a]`. We don't do this hoisting by default, but the
//! [`Hoister`] struct can be configured to do so.
//!
//! It's also important to note that canonizalization doesn't imply any form of semantic equality
//! and it is just a best effort to facilitate syntactic manipulation. For example, the types
//! `∃a,b. (i32[a], i32[b])` and `∃a,b. (i32[b], i32[a])` are semantically equal but hoisting won't
//! account for it.
//!
//! [existentials]: TyKind::Exists
//! [constraint predicates]: TyKind::Constr
use flux_arc_interner::List;
use rustc_ast::Mutability;
use rustc_type_ir::{BoundVar, INNERMOST};

use super::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    BaseTy, Binder, BoundVariableKind, Expr, GenericArg, GenericArgsExt, SubsetTy, SubsetTyCtor,
    Ty, TyCtor, TyKind,
};
use crate::rty::fold::TypeVisitable;

#[derive(Default)]
pub struct Hoister<D> {
    delegate: D,
    tuples: bool,
    shr_refs: bool,
    boxes: bool,
}

pub trait HoisterDelegate {
    fn hoist_exists(&mut self, ty_ctor: &TyCtor) -> Ty;
    fn hoist_constr(&mut self, pred: Expr);
}

impl<D> Hoister<D> {
    pub fn with_delegate(delegate: D) -> Self {
        Hoister { delegate, tuples: false, shr_refs: false, boxes: false }
    }

    pub fn hoist_inside_shr_refs(mut self, shr_refs: bool) -> Self {
        self.shr_refs = shr_refs;
        self
    }

    pub fn hoist_inside_tuples(mut self, tuples: bool) -> Self {
        self.tuples = tuples;
        self
    }

    pub fn hoist_inside_boxes(mut self, boxes: bool) -> Self {
        self.boxes = boxes;
        self
    }
}

impl<D: HoisterDelegate> Hoister<D> {
    pub fn hoist(&mut self, ty: &Ty) -> Ty {
        ty.fold_with(self)
    }
}

impl<D: HoisterDelegate> TypeFolder for Hoister<D> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idx) => Ty::indexed(bty.fold_with(self), idx.clone()),
            TyKind::Exists(ty_ctor) => self.delegate.hoist_exists(ty_ctor).fold_with(self),
            TyKind::Constr(pred, ty) => {
                self.delegate.hoist_constr(pred.clone());
                ty.fold_with(self)
            }
            TyKind::StrgRef(re, path, ty) => Ty::strg_ref(*re, path.clone(), ty.fold_with(self)),
            TyKind::Downcast(..) => ty.super_fold_with(self),
            _ => ty.clone(),
        }
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, args) if adt_def.is_box() && self.boxes => {
                let (boxed, alloc) = args.box_args();
                let args = List::from_arr([
                    GenericArg::Ty(boxed.fold_with(self)),
                    GenericArg::Ty(alloc.clone()),
                ]);
                BaseTy::Adt(adt_def.clone(), args)
            }
            BaseTy::Ref(re, ty, Mutability::Not) if self.shr_refs => {
                BaseTy::Ref(*re, ty.fold_with(self), Mutability::Not)
            }
            BaseTy::Tuple(tys) if self.tuples => BaseTy::Tuple(tys.fold_with(self)),
            _ => bty.clone(),
        }
    }
}

#[derive(Default)]
pub struct BoundedHoister {
    vars: Vec<BoundVariableKind>,
    preds: Vec<Expr>,
}

impl BoundedHoister {
    pub fn bind<T>(self, f: impl FnOnce(List<BoundVariableKind>, Vec<Expr>) -> T) -> Binder<T> {
        let vars = List::from_vec(self.vars);
        Binder::bind_with_vars(f(vars.clone(), self.preds), vars)
    }
}

impl HoisterDelegate for &mut BoundedHoister {
    fn hoist_exists(&mut self, ty_ctor: &TyCtor) -> Ty {
        ty_ctor.replace_bound_refts_with(|sort, mode, kind| {
            let idx = self.vars.len();
            self.vars
                .push(BoundVariableKind::Refine(sort.clone(), mode, kind));
            Expr::bvar(INNERMOST, BoundVar::from_usize(idx), kind)
        })
    }

    fn hoist_constr(&mut self, pred: Expr) {
        self.preds.push(pred);
    }
}

impl Ty {
    /// Hoist existentials and predicates inside the type stopping when encountering the first
    /// type constructor.
    pub fn shallow_canonicalize(&self) -> CanonicalTy {
        debug_assert!(!self.has_escaping_bvars());
        let mut delegate = BoundedHoister::default();
        let ty = Hoister::with_delegate(&mut delegate).hoist(self);
        let constr_ty = delegate.bind(|_, preds| {
            let pred = Expr::and_from_iter(preds);
            CanonicalConstrTy { ty, pred }
        });
        if constr_ty.vars().is_empty() {
            CanonicalTy::Constr(constr_ty.skip_binder())
        } else {
            CanonicalTy::Exists(constr_ty)
        }
    }
}

pub struct CanonicalConstrTy {
    /// Guaranteed to not have any (shallow) [existential] or [constraint] types
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
/// When canonicalizing a type without a [constraint] type, `p` will be [`Expr::tt()`].
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
                        Expr::and(&constr.pred, Expr::eq(Expr::nu(), idx)),
                    );
                    Some(Binder::bind_with_sort(constr, sort))
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
                        cx.fmt_bound_vars(false, "∃", poly_constr.vars(), ". ", f)?;
                        w!("{:?}", poly_constr.as_ref().skip_binder())
                    })
                }
            }
        }
    }

    impl_debug_with_default_cx!(CanonicalTy, CanonicalConstrTy);
}
