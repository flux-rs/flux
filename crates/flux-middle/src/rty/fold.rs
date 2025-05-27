//! This modules follows the implementation of folding in rustc. For more information read the
//! documentation in [`rustc_middle::ty::fold`].

use std::ops::ControlFlow;

use flux_arc_interner::{Internable, List};
use flux_common::bug;
use itertools::Itertools;
use rustc_hash::FxHashSet;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{
    BaseTy, Binder, BoundVariableKinds, Const, EVid, Ensures, Expr, ExprKind, GenericArg, Name,
    OutlivesPredicate, PolyFuncSort, PtrKind, ReBound, ReErased, Region, Sort, SubsetTy, Ty,
    TyKind, normalize::Normalizer,
};
use crate::{
    global_env::GlobalEnv,
    rty::{expr::HoleKind, EarlyReftParam, Var, VariantSig},
};

pub trait TypeVisitor: Sized {
    type BreakTy = !;

    fn visit_binder<T: TypeVisitable>(&mut self, t: &Binder<T>) -> ControlFlow<Self::BreakTy> {
        t.super_visit_with(self)
    }

    fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::BreakTy> {
        expr.super_visit_with(self)
    }

    fn visit_sort(&mut self, sort: &Sort) -> ControlFlow<Self::BreakTy> {
        sort.super_visit_with(self)
    }

    fn visit_ty(&mut self, ty: &Ty) -> ControlFlow<Self::BreakTy> {
        ty.super_visit_with(self)
    }

    fn visit_bty(&mut self, bty: &BaseTy) -> ControlFlow<Self::BreakTy> {
        bty.super_visit_with(self)
    }
}

pub trait FallibleTypeFolder: Sized {
    type Error;

    fn try_fold_binder<T: TypeFoldable>(
        &mut self,
        t: &Binder<T>,
    ) -> Result<Binder<T>, Self::Error> {
        t.try_super_fold_with(self)
    }

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, Self::Error> {
        sort.try_super_fold_with(self)
    }

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, Self::Error> {
        ty.try_super_fold_with(self)
    }

    fn try_fold_bty(&mut self, bty: &BaseTy) -> Result<BaseTy, Self::Error> {
        bty.try_super_fold_with(self)
    }

    fn try_fold_subset_ty(&mut self, constr: &SubsetTy) -> Result<SubsetTy, Self::Error> {
        constr.try_super_fold_with(self)
    }

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, Self::Error> {
        Ok(*re)
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, Self::Error> {
        c.try_super_fold_with(self)
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        expr.try_super_fold_with(self)
    }
}

pub trait TypeFolder: FallibleTypeFolder<Error = !> {
    fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
        t.super_fold_with(self)
    }

    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        sort.super_fold_with(self)
    }

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        ty.super_fold_with(self)
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        bty.super_fold_with(self)
    }

    fn fold_subset_ty(&mut self, constr: &SubsetTy) -> SubsetTy {
        constr.super_fold_with(self)
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        *re
    }

    fn fold_const(&mut self, c: &Const) -> Const {
        c.super_fold_with(self)
    }

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        expr.super_fold_with(self)
    }
}

impl<F> FallibleTypeFolder for F
where
    F: TypeFolder,
{
    type Error = !;

    fn try_fold_binder<T: TypeFoldable>(
        &mut self,
        t: &Binder<T>,
    ) -> Result<Binder<T>, Self::Error> {
        Ok(self.fold_binder(t))
    }

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, Self::Error> {
        Ok(self.fold_sort(sort))
    }

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, Self::Error> {
        Ok(self.fold_ty(ty))
    }

    fn try_fold_bty(&mut self, bty: &BaseTy) -> Result<BaseTy, Self::Error> {
        Ok(self.fold_bty(bty))
    }

    fn try_fold_subset_ty(&mut self, ty: &SubsetTy) -> Result<SubsetTy, Self::Error> {
        Ok(self.fold_subset_ty(ty))
    }

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, Self::Error> {
        Ok(self.fold_region(re))
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, Self::Error> {
        Ok(self.fold_const(c))
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        Ok(self.fold_expr(expr))
    }
}

pub trait TypeVisitable: Sized {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy>;

    fn has_escaping_bvars(&self) -> bool {
        self.has_escaping_bvars_at_or_above(INNERMOST)
    }

    /// Returns `true` if `self` has any late-bound vars that are either
    /// bound by `binder` or bound by some binder outside of `binder`.
    /// If `binder` is `ty::INNERMOST`, this indicates whether
    /// there are any late-bound vars that appear free.
    fn has_escaping_bvars_at_or_above(&self, binder: DebruijnIndex) -> bool {
        struct HasEscapingVars {
            /// Anything bound by `outer_index` or "above" is escaping.
            outer_index: DebruijnIndex,
        }

        impl TypeVisitor for HasEscapingVars {
            type BreakTy = ();

            fn visit_binder<T: TypeVisitable>(&mut self, t: &Binder<T>) -> ControlFlow<()> {
                self.outer_index.shift_in(1);
                t.super_visit_with(self);
                self.outer_index.shift_out(1);
                ControlFlow::Continue(())
            }

            // TODO(nilehmann) keep track of the outermost binder to optimize this, i.e.,
            // what rustc calls outer_exclusive_binder.
            fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<()> {
                if let ExprKind::Var(Var::Bound(debruijn, _)) = expr.kind() {
                    if *debruijn >= self.outer_index {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                } else {
                    expr.super_visit_with(self)
                }
            }
        }
        let mut visitor = HasEscapingVars { outer_index: binder };
        self.visit_with(&mut visitor).is_break()
    }

    /// Returns the set of all free variables.
    /// For example, `Vec<i32[n]>{v : v > m}` returns `{n, m}`.
    fn fvars(&self) -> FxHashSet<Name> {
        struct CollectFreeVars(FxHashSet<Name>);

        impl TypeVisitor for CollectFreeVars {
            fn visit_expr(&mut self, e: &Expr) -> ControlFlow<Self::BreakTy> {
                if let ExprKind::Var(Var::Free(name)) = e.kind() {
                    self.0.insert(*name);
                }
                e.super_visit_with(self)
            }
        }

        let mut collector = CollectFreeVars(FxHashSet::default());
        self.visit_with(&mut collector);
        collector.0
    }

    fn early_params(&self) -> FxHashSet<EarlyReftParam> {
        struct CollectEarlyParams(FxHashSet<EarlyReftParam>);

        impl TypeVisitor for CollectEarlyParams {
            fn visit_expr(&mut self, e: &Expr) -> ControlFlow<Self::BreakTy> {
                if let ExprKind::Var(Var::EarlyParam(param)) = e.kind() {
                    self.0.insert(*param);
                }
                e.super_visit_with(self)
            }
        }

        let mut collector = CollectEarlyParams(FxHashSet::default());
        self.visit_with(&mut collector);
        collector.0
    }
}

pub trait TypeSuperVisitable: TypeVisitable {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy>;
}

pub trait TypeFoldable: TypeVisitable {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error>;

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.try_fold_with(folder).into_ok()
    }

    /// Normalize expressions by applying beta reductions for tuples and lambda abstractions.
    fn normalize(&self, genv: GlobalEnv) -> Self {
        self.fold_with(&mut Normalizer::new(genv, None))
    }

    /// Replaces all [holes] with the result of calling a closure. The closure takes a list with
    /// all the *layers* of [bound] variables at the point the hole was found. Each layer corresponds
    /// to the list of bound variables at that level. The list is ordered from outermost to innermost
    /// binder, i.e., the last element is the binder closest to the hole.
    ///
    /// [holes]: ExprKind::Hole
    /// [bound]: Binder
    fn replace_holes(&self, f: impl FnMut(&[BoundVariableKinds], HoleKind) -> Expr) -> Self {
        struct ReplaceHoles<F>(F, Vec<BoundVariableKinds>);

        impl<F> TypeFolder for ReplaceHoles<F>
        where
            F: FnMut(&[BoundVariableKinds], HoleKind) -> Expr,
        {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.1.push(t.vars().clone());
                let t = t.super_fold_with(self);
                self.1.pop();
                t
            }

            fn fold_expr(&mut self, e: &Expr) -> Expr {
                if let ExprKind::Hole(kind) = e.kind() {
                    self.0(&self.1, kind.clone())
                } else {
                    e.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut ReplaceHoles(f, vec![]))
    }

    /// Remove all refinements and turn each underlying [`BaseTy`] into a [`TyKind::Exists`] with a
    /// [`TyKind::Constr`] and a [`hole`]. For example, `Vec<{v. i32[v] | v > 0}>[n]` becomes
    /// `{n. Vec<{v. i32[v] | *}>[n] | *}`.
    ///
    /// [`hole`]: ExprKind::Hole
    fn with_holes(&self) -> Self {
        struct WithHoles;

        impl TypeFolder for WithHoles {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                if let Some(bty) = ty.as_bty_skipping_existentials() {
                    Ty::exists_with_constr(bty.fold_with(self), Expr::hole(HoleKind::Pred))
                } else {
                    ty.super_fold_with(self)
                }
            }

            fn fold_subset_ty(&mut self, constr: &SubsetTy) -> SubsetTy {
                SubsetTy::new(constr.bty.clone(), constr.idx.clone(), Expr::hole(HoleKind::Pred))
            }
        }

        self.fold_with(&mut WithHoles)
    }

    fn replace_evars(&self, f: &mut impl FnMut(EVid) -> Option<Expr>) -> Result<Self, EVid> {
        struct Folder<F>(F);
        impl<F: FnMut(EVid) -> Option<Expr>> FallibleTypeFolder for Folder<F> {
            type Error = EVid;

            fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
                if let ExprKind::Var(Var::EVar(evid)) = expr.kind() {
                    if let Some(sol) = (self.0)(*evid) { Ok(sol.clone()) } else { Err(*evid) }
                } else {
                    expr.try_super_fold_with(self)
                }
            }
        }

        self.try_fold_with(&mut Folder(f))
    }

    fn shift_in_escaping(&self, amount: u32) -> Self {
        struct Shifter {
            current_index: DebruijnIndex,
            amount: u32,
        }

        impl TypeFolder for Shifter {
            fn fold_binder<T>(&mut self, t: &Binder<T>) -> Binder<T>
            where
                T: TypeFoldable,
            {
                self.current_index.shift_in(1);
                let r = t.super_fold_with(self);
                self.current_index.shift_out(1);
                r
            }

            fn fold_region(&mut self, re: &Region) -> Region {
                if let ReBound(debruijn, br) = *re
                    && debruijn >= self.current_index
                {
                    ReBound(debruijn.shifted_in(self.amount), br)
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::Bound(debruijn, breft)) = expr.kind()
                    && *debruijn >= self.current_index
                {
                    Expr::bvar(debruijn.shifted_in(self.amount), breft.var, breft.kind)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }

    fn shift_out_escaping(&self, amount: u32) -> Self {
        struct Shifter {
            amount: u32,
            current_index: DebruijnIndex,
        }

        impl TypeFolder for Shifter {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.current_index.shift_in(1);
                let t = t.super_fold_with(self);
                self.current_index.shift_out(1);
                t
            }

            fn fold_region(&mut self, re: &Region) -> Region {
                if let ReBound(debruijn, br) = *re
                    && debruijn >= self.current_index
                {
                    ReBound(debruijn.shifted_out(self.amount), br)
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::Bound(debruijn, breft)) = expr.kind()
                    && debruijn >= &self.current_index
                {
                    Expr::bvar(debruijn.shifted_out(self.amount), breft.var, breft.kind)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }

    fn erase_regions(&self) -> Self {
        struct RegionEraser;
        impl TypeFolder for RegionEraser {
            fn fold_region(&mut self, r: &Region) -> Region {
                match *r {
                    ReBound(..) => *r,
                    _ => ReErased,
                }
            }
        }

        self.fold_with(&mut RegionEraser)
    }

    fn replace_free_vars(&self, f: &mut impl FnMut(Name) -> Option<Expr>) -> Self {
        struct Folder<F>(F);
        impl<F: FnMut(Name) -> Option<Expr>> TypeFolder for Folder<F> {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::Free(name)) = expr.kind() {
                    if let Some(sol) = (self.0)(*name) { sol.clone() } else { expr.clone() }
                } else {
                    expr.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut Folder(f))
    }
}

pub trait TypeSuperFoldable: TypeFoldable {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error>;

    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.try_super_fold_with(folder).into_ok()
    }
}

impl<T: TypeVisitable> TypeVisitable for OutlivesPredicate<T> {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.0.visit_with(visitor)?;
        self.1.visit_with(visitor)
    }
}

impl<T: TypeFoldable> TypeFoldable for OutlivesPredicate<T> {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(OutlivesPredicate(self.0.try_fold_with(folder)?, self.1.try_fold_with(folder)?))
    }
}

impl TypeVisitable for Sort {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_sort(self)
    }
}

impl TypeSuperVisitable for Sort {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Sort::Tuple(sorts) => sorts.visit_with(visitor),
            Sort::App(_, args) => args.visit_with(visitor),
            Sort::Func(fsort) => fsort.visit_with(visitor),
            Sort::Alias(_, alias_ty) => alias_ty.visit_with(visitor),
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::Str
            | Sort::Char
            | Sort::BitVec(_)
            | Sort::Loc
            | Sort::Param(_)
            | Sort::Var(_)
            | Sort::Infer(_)
            | Sort::Err => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for Sort {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_sort(self)
    }
}

impl TypeSuperFoldable for Sort {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let sort = match self {
            Sort::Tuple(sorts) => Sort::tuple(sorts.try_fold_with(folder)?),
            Sort::App(ctor, sorts) => Sort::app(ctor.clone(), sorts.try_fold_with(folder)?),
            Sort::Func(fsort) => Sort::Func(fsort.try_fold_with(folder)?),
            Sort::Alias(kind, alias_ty) => Sort::Alias(*kind, alias_ty.try_fold_with(folder)?),
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::Loc
            | Sort::Str
            | Sort::Char
            | Sort::BitVec(_)
            | Sort::Param(_)
            | Sort::Var(_)
            | Sort::Infer(_)
            | Sort::Err => self.clone(),
        };
        Ok(sort)
    }
}

impl TypeVisitable for PolyFuncSort {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.fsort.visit_with(visitor)
    }
}

impl TypeFoldable for PolyFuncSort {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(PolyFuncSort { params: self.params.clone(), fsort: self.fsort.try_fold_with(folder)? })
    }
}

impl<T> TypeVisitable for Binder<T>
where
    T: TypeVisitable,
{
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_binder(self)
    }
}

impl<T> TypeSuperVisitable for Binder<T>
where
    T: TypeVisitable,
{
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.skip_binder_ref().visit_with(visitor)
    }
}

impl<T> TypeFoldable for Binder<T>
where
    T: TypeFoldable,
{
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_binder(self)
    }
}

impl<T> TypeSuperFoldable for Binder<T>
where
    T: TypeFoldable,
{
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(Binder::bind_with_vars(
            self.skip_binder_ref().try_fold_with(folder)?,
            self.vars().try_fold_with(folder)?,
        ))
    }
}

impl TypeVisitable for VariantSig {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.fields.visit_with(visitor)?;
        self.idx.visit_with(visitor)
    }
}

impl TypeFoldable for VariantSig {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let args = self.args.try_fold_with(folder)?;
        let fields = self.fields.try_fold_with(folder)?;
        let idx = self.idx.try_fold_with(folder)?;
        let requires = self.requires.try_fold_with(folder)?;
        Ok(VariantSig::new(self.adt_def.clone(), args, fields, idx, requires))
    }
}

impl<T: TypeVisitable> TypeVisitable for Vec<T> {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.iter().try_for_each(|t| t.visit_with(visitor))
    }
}

impl TypeVisitable for Ensures {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Ensures::Type(path, ty) => {
                path.to_expr().visit_with(visitor)?;
                ty.visit_with(visitor)
            }
            Ensures::Pred(e) => e.visit_with(visitor),
        }
    }
}

impl TypeFoldable for Ensures {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let c = match self {
            Ensures::Type(path, ty) => {
                let path_expr = path.to_expr().try_fold_with(folder)?;
                Ensures::Type(
                    path_expr.to_path().unwrap_or_else(|| {
                        bug!("invalid path `{path_expr:?}` produced when folding `{self:?}`",)
                    }),
                    ty.try_fold_with(folder)?,
                )
            }
            Ensures::Pred(e) => Ensures::Pred(e.try_fold_with(folder)?),
        };
        Ok(c)
    }
}

impl TypeVisitable for Ty {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_ty(self)
    }
}

impl TypeSuperVisitable for Ty {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                bty.visit_with(visitor)?;
                idxs.visit_with(visitor)
            }
            TyKind::Exists(exists) => exists.visit_with(visitor),
            TyKind::StrgRef(_, path, ty) => {
                path.to_expr().visit_with(visitor)?;
                ty.visit_with(visitor)
            }
            TyKind::Ptr(_, path) => path.to_expr().visit_with(visitor),
            TyKind::Constr(pred, ty) => {
                pred.visit_with(visitor)?;
                ty.visit_with(visitor)
            }
            TyKind::Downcast(.., args, _, fields) => {
                args.visit_with(visitor)?;
                fields.visit_with(visitor)
            }
            TyKind::Blocked(ty) => ty.visit_with(visitor),
            TyKind::Infer(_) | TyKind::Param(_) | TyKind::Discr(..) | TyKind::Uninit => {
                ControlFlow::Continue(())
            }
        }
    }
}

impl TypeFoldable for Ty {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_ty(self)
    }
}

impl TypeSuperFoldable for Ty {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Ty, F::Error> {
        let ty = match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                Ty::indexed(bty.try_fold_with(folder)?, idxs.try_fold_with(folder)?)
            }
            TyKind::Exists(exists) => TyKind::Exists(exists.try_fold_with(folder)?).intern(),
            TyKind::StrgRef(re, path, ty) => {
                Ty::strg_ref(
                    re.try_fold_with(folder)?,
                    path.to_expr()
                        .try_fold_with(folder)?
                        .to_path()
                        .expect("type folding produced an invalid path"),
                    ty.try_fold_with(folder)?,
                )
            }
            TyKind::Ptr(pk, path) => {
                let pk = match pk {
                    PtrKind::Mut(re) => PtrKind::Mut(re.try_fold_with(folder)?),
                    PtrKind::Box => PtrKind::Box,
                };
                Ty::ptr(
                    pk,
                    path.to_expr()
                        .try_fold_with(folder)?
                        .to_path()
                        .expect("type folding produced an invalid path"),
                )
            }
            TyKind::Constr(pred, ty) => {
                Ty::constr(pred.try_fold_with(folder)?, ty.try_fold_with(folder)?)
            }
            TyKind::Downcast(adt, args, ty, variant, fields) => {
                Ty::downcast(
                    adt.clone(),
                    args.clone(),
                    ty.clone(),
                    *variant,
                    fields.try_fold_with(folder)?,
                )
            }
            TyKind::Blocked(ty) => Ty::blocked(ty.try_fold_with(folder)?),
            TyKind::Infer(_) | TyKind::Param(_) | TyKind::Uninit | TyKind::Discr(..) => {
                self.clone()
            }
        };
        Ok(ty)
    }
}

impl TypeVisitable for Region {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::Continue(())
    }
}

impl TypeFoldable for Region {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_region(self)
    }
}

impl TypeSuperFoldable for Const {
    fn try_super_fold_with<F: FallibleTypeFolder>(
        &self,
        _folder: &mut F,
    ) -> Result<Self, F::Error> {
        // FIXME(nilehmann) we are not folding the type in `ConstKind::Value` because it's a rustc::ty::Ty
        Ok(self.clone())
    }
}

impl TypeVisitable for Const {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy> {
        ControlFlow::Continue(())
    }
}

impl TypeFoldable for Const {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_const(self)
    }
}

impl TypeVisitable for BaseTy {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_bty(self)
    }
}

impl TypeSuperVisitable for BaseTy {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            BaseTy::Adt(_, args) => args.visit_with(visitor),
            BaseTy::FnDef(_, args) => args.visit_with(visitor),
            BaseTy::Slice(ty) => ty.visit_with(visitor),
            BaseTy::RawPtr(ty, _) => ty.visit_with(visitor),
            BaseTy::Ref(_, ty, _) => ty.visit_with(visitor),
            BaseTy::FnPtr(poly_fn_sig) => poly_fn_sig.visit_with(visitor),
            BaseTy::Tuple(tys) => tys.visit_with(visitor),
            BaseTy::Alias(_, alias_ty) => alias_ty.visit_with(visitor),
            BaseTy::Array(ty, _) => ty.visit_with(visitor),
            BaseTy::Coroutine(_, resume_ty, upvars) => {
                resume_ty.visit_with(visitor)?;
                upvars.visit_with(visitor)
            }
            BaseTy::Dynamic(exi_preds, _) => exi_preds.visit_with(visitor),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Closure(..)
            | BaseTy::Never
            | BaseTy::Infer(_)
            | BaseTy::Foreign(_)
            | BaseTy::Param(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for BaseTy {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_bty(self)
    }
}

impl TypeSuperFoldable for BaseTy {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let bty = match self {
            BaseTy::Adt(adt_def, args) => BaseTy::adt(adt_def.clone(), args.try_fold_with(folder)?),
            BaseTy::FnDef(def_id, args) => BaseTy::fn_def(*def_id, args.try_fold_with(folder)?),
            BaseTy::Foreign(def_id) => BaseTy::Foreign(*def_id),
            BaseTy::Slice(ty) => BaseTy::Slice(ty.try_fold_with(folder)?),
            BaseTy::RawPtr(ty, mu) => BaseTy::RawPtr(ty.try_fold_with(folder)?, *mu),
            BaseTy::Ref(re, ty, mutbl) => {
                BaseTy::Ref(re.try_fold_with(folder)?, ty.try_fold_with(folder)?, *mutbl)
            }
            BaseTy::FnPtr(decl) => BaseTy::FnPtr(decl.try_fold_with(folder)?),
            BaseTy::Tuple(tys) => BaseTy::Tuple(tys.try_fold_with(folder)?),
            BaseTy::Alias(kind, alias_ty) => BaseTy::Alias(*kind, alias_ty.try_fold_with(folder)?),
            BaseTy::Array(ty, c) => {
                BaseTy::Array(ty.try_fold_with(folder)?, c.try_fold_with(folder)?)
            }
            BaseTy::Closure(did, args, gen_args) => {
                BaseTy::Closure(*did, args.try_fold_with(folder)?, gen_args.clone())
            }
            BaseTy::Coroutine(did, resume_ty, args) => {
                BaseTy::Coroutine(
                    *did,
                    resume_ty.try_fold_with(folder)?,
                    args.try_fold_with(folder)?,
                )
            }
            BaseTy::Dynamic(preds, region) => {
                BaseTy::Dynamic(preds.try_fold_with(folder)?, region.try_fold_with(folder)?)
            }
            BaseTy::Int(_)
            | BaseTy::Param(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Infer(_)
            | BaseTy::Never => self.clone(),
        };
        Ok(bty)
    }
}

impl TypeVisitable for SubsetTy {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.bty.visit_with(visitor)?;
        self.idx.visit_with(visitor)?;
        self.pred.visit_with(visitor)
    }
}

impl TypeFoldable for SubsetTy {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_subset_ty(self)
    }
}

impl TypeSuperFoldable for SubsetTy {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(SubsetTy {
            bty: self.bty.try_fold_with(folder)?,
            idx: self.idx.try_fold_with(folder)?,
            pred: self.pred.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for GenericArg {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::Base(ty) => ty.visit_with(visitor),
            GenericArg::Lifetime(_) => ControlFlow::Continue(()),
            GenericArg::Const(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for GenericArg {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let arg = match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.try_fold_with(folder)?),
            GenericArg::Base(ctor) => GenericArg::Base(ctor.try_fold_with(folder)?),
            GenericArg::Lifetime(re) => GenericArg::Lifetime(re.try_fold_with(folder)?),
            GenericArg::Const(c) => GenericArg::Const(c.try_fold_with(folder)?),
        };
        Ok(arg)
    }
}

impl TypeVisitable for Expr {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_expr(self)
    }
}

impl TypeSuperVisitable for Expr {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self.kind() {
            ExprKind::Var(_) => ControlFlow::Continue(()),
            ExprKind::BinaryOp(_, e1, e2) => {
                e1.visit_with(visitor)?;
                e2.visit_with(visitor)
            }
            ExprKind::Tuple(flds) => flds.visit_with(visitor),
            ExprKind::Ctor(_, flds) => flds.visit_with(visitor),
            ExprKind::FieldProj(e, _) | ExprKind::PathProj(e, _) | ExprKind::UnaryOp(_, e) => {
                e.visit_with(visitor)
            }
            ExprKind::App(func, arg) => {
                func.visit_with(visitor)?;
                arg.visit_with(visitor)
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                p.visit_with(visitor)?;
                e1.visit_with(visitor)?;
                e2.visit_with(visitor)
            }
            ExprKind::KVar(kvar) => kvar.visit_with(visitor),
            ExprKind::WKVar(wkvar) => wkvar.visit_with(visitor),
            ExprKind::Alias(alias, args) => {
                alias.visit_with(visitor)?;
                args.visit_with(visitor)
            }
            ExprKind::Abs(body) => body.visit_with(visitor),
            ExprKind::BoundedQuant(_, _, body) => body.visit_with(visitor),
            ExprKind::ForAll(expr) => expr.visit_with(visitor),
            ExprKind::Let(init, body) => {
                init.visit_with(visitor)?;
                body.visit_with(visitor)
            }
            ExprKind::Constant(_)
            | ExprKind::Hole(_)
            | ExprKind::Local(_)
            | ExprKind::GlobalFunc(..)
            | ExprKind::ConstDefId(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for Expr {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_expr(self)
    }
}

impl TypeSuperFoldable for Expr {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let span = self.span();
        let expr = match self.kind() {
            ExprKind::Var(var) => Expr::var(*var),
            ExprKind::Local(local) => Expr::local(*local),
            ExprKind::Constant(c) => Expr::constant(*c),
            ExprKind::ConstDefId(did) => Expr::const_def_id(*did),
            ExprKind::BinaryOp(op, e1, e2) => {
                Expr::binary_op(
                    op.try_fold_with(folder)?,
                    e1.try_fold_with(folder)?,
                    e2.try_fold_with(folder)?,
                )
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.try_fold_with(folder)?),
            ExprKind::FieldProj(e, proj) => Expr::field_proj(e.try_fold_with(folder)?, *proj),
            ExprKind::Tuple(flds) => Expr::tuple(flds.try_fold_with(folder)?),
            ExprKind::Ctor(ctor, flds) => Expr::ctor(*ctor, flds.try_fold_with(folder)?),
            ExprKind::PathProj(e, field) => Expr::path_proj(e.try_fold_with(folder)?, *field),
            ExprKind::App(func, arg) => {
                Expr::app(func.try_fold_with(folder)?, arg.try_fold_with(folder)?)
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                Expr::ite(
                    p.try_fold_with(folder)?,
                    e1.try_fold_with(folder)?,
                    e2.try_fold_with(folder)?,
                )
            }
            ExprKind::Hole(kind) => Expr::hole(kind.try_fold_with(folder)?),
            ExprKind::KVar(kvar) => Expr::kvar(kvar.try_fold_with(folder)?),
            ExprKind::WKVar(wkvar) => Expr::wkvar(wkvar.try_fold_with(folder)?),
            ExprKind::Abs(lam) => Expr::abs(lam.try_fold_with(folder)?),
            ExprKind::BoundedQuant(kind, rng, body) => {
                Expr::bounded_quant(*kind, *rng, body.try_fold_with(folder)?)
            }
            ExprKind::GlobalFunc(kind) => Expr::global_func(*kind),
            ExprKind::Alias(alias, args) => {
                Expr::alias(alias.try_fold_with(folder)?, args.try_fold_with(folder)?)
            }
            ExprKind::ForAll(expr) => Expr::forall(expr.try_fold_with(folder)?),
            ExprKind::Let(init, body) => {
                Expr::let_(init.try_fold_with(folder)?, body.try_fold_with(folder)?)
            }
        };
        Ok(expr.at_opt(span))
    }
}

impl<T> TypeVisitable for List<T>
where
    T: TypeVisitable,
    [T]: Internable,
{
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.iter().try_for_each(|t| t.visit_with(visitor))
    }
}

impl<S, T> TypeVisitable for (S, T)
where
    S: TypeVisitable,
    T: TypeVisitable,
{
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.0.visit_with(visitor)?;
        self.1.visit_with(visitor)
    }
}

impl<T> TypeFoldable for List<T>
where
    T: TypeFoldable,
    [T]: Internable,
{
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        self.iter().map(|t| t.try_fold_with(folder)).try_collect()
    }
}

impl<S, T> TypeFoldable for (S, T)
where
    S: TypeFoldable,
    T: TypeFoldable,
{
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok((self.0.try_fold_with(folder)?, self.1.try_fold_with(folder)?))
    }
}

/// Used for types that are `Copy` and which **do not care arena allocated data** (i.e., don't need
/// to be folded).
macro_rules! TrivialTypeTraversalImpls {
    ($($ty:ty,)+) => {
        $(
            impl $crate::rty::fold::TypeFoldable for $ty {
                fn try_fold_with<F: $crate::rty::fold::FallibleTypeFolder>(
                    &self,
                    _: &mut F,
                ) -> ::std::result::Result<Self, F::Error> {
                    Ok(*self)
                }

                #[inline]
                fn fold_with<F: $crate::rty::fold::TypeFolder>(
                    &self,
                    _: &mut F,
                ) -> Self {
                    *self
                }
            }

            impl $crate::rty::fold::TypeVisitable for $ty {
                #[inline]
                fn visit_with<V: $crate::rty::fold::TypeVisitor>(
                    &self,
                    _: &mut V)
                    -> ::core::ops::ControlFlow<V::BreakTy>
                {
                    ::core::ops::ControlFlow::Continue(())
                }
            }
        )+
    };
}

// For things that don't carry any arena-allocated data (and are copy...), just add them to this list.
TrivialTypeTraversalImpls! {
    (),
    bool,
    usize,
    crate::fhir::InferMode,
    crate::rty::BoundReftKind,
    crate::rty::BvSize,
    crate::rty::KVid,
    crate::def_id::FluxDefId,
    crate::def_id::FluxLocalDefId,
    rustc_span::Symbol,
    rustc_hir::def_id::DefId,
    rustc_hir::Safety,
    rustc_target::spec::abi::Abi,
    rustc_type_ir::ClosureKind,
    flux_rustc_bridge::ty::BoundRegionKind,
}
