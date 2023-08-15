//! This modules folows the implementation of folding in rustc. For more information read the
//! documentation in [`rustc_middle::ty::fold`].

use std::ops::ControlFlow;

use flux_common::{bug, iter::IterExt};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{
    evars::EVarSol,
    normalize::{Defns, Normalizer},
    subst::EVarSubstFolder,
    AliasTy, BaseTy, Binder, BoundVariableKind, Clause, ClauseKind, Constraint, Expr, ExprKind,
    FnOutput, FnSig, FnTraitPredicate, FuncSort, GeneratorObligPredicate, GenericArg, Index,
    Invariant, KVar, Name, Opaqueness, ProjectionPredicate, PtrKind, Qualifier, ReLateBound,
    Region, Sort, Ty, TyKind,
};
use crate::{
    intern::{Internable, List},
    rty::{AliasKind, Var, VariantSig},
};

pub trait TypeVisitor: Sized {
    type BreakTy = !;

    fn visit_binder<T: TypeVisitable>(&mut self, t: &Binder<T>) -> ControlFlow<Self::BreakTy> {
        t.super_visit_with(self)
    }

    fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::BreakTy> {
        expr.super_visit_with(self)
    }

    fn visit_fvar(&mut self, _name: Name) -> ControlFlow<Self::BreakTy> {
        ControlFlow::Continue(())
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

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, Self::Error> {
        Ok(*re)
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

    fn fold_region(&mut self, re: &Region) -> Region {
        *re
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

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, Self::Error> {
        Ok(self.fold_region(re))
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        Ok(self.fold_expr(expr))
    }
}

pub trait TypeVisitable: Sized {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()>;

    fn has_escaping_bvars(&self) -> bool {
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
                if let ExprKind::Var(Var::LateBound(debruijn, _)) = expr.kind() {
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
        let mut visitor = HasEscapingVars { outer_index: INNERMOST };
        self.visit_with(&mut visitor).is_break()
    }

    /// Returns the set of all free variables.
    /// For example, `Vec<i32[n]>{v : v > m}` returns `{n, m}`.
    fn fvars(&self) -> FxHashSet<Name> {
        struct CollectFreeVars(FxHashSet<Name>);

        impl TypeVisitor for CollectFreeVars {
            fn visit_fvar(&mut self, name: Name) -> ControlFlow<Self::BreakTy> {
                self.0.insert(name);
                ControlFlow::Continue(())
            }
        }

        let mut collector = CollectFreeVars(FxHashSet::default());
        self.visit_with(&mut collector);
        collector.0
    }

    /// Returns the set of all free variables.
    /// For example, `Vec<i32[n]>{v : v > m}` returns `{n, m}`.
    fn opaque_def_ids(&self) -> FxHashSet<DefId> {
        struct CollectOpaqueDefIds(FxHashSet<DefId>);

        impl TypeVisitor for CollectOpaqueDefIds {
            fn visit_bty(&mut self, bty: &BaseTy) -> ControlFlow<Self::BreakTy> {
                match bty {
                    BaseTy::Alias(AliasKind::Opaque, alias_ty) => {
                        let _ = self.0.insert(alias_ty.def_id);
                        alias_ty.args.visit_with(self)
                    }
                    _ => ControlFlow::Continue(()),
                }
            }
        }

        let mut collector = CollectOpaqueDefIds(FxHashSet::default());
        self.visit_with(&mut collector);
        collector.0
    }
}

pub trait TypeSuperVisitable: TypeVisitable {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()>;
}

pub trait TypeFoldable: TypeVisitable {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error>;

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.try_fold_with(folder).into_ok()
    }

    /// Normalize expressions by applying beta reductions for tuples and lambda abstractions.
    fn normalize(&self, defns: &Defns) -> Self {
        self.fold_with(&mut Normalizer::new(defns))
    }

    /// Replaces all [`holes`] with a fresh predicate generated by calling `mk_pred`. The function
    /// `mk_pred` takes a list with the sorts of all bound variables at the point the hole was found.
    /// The list is ordered from outermost to innermost binder, i.e., the last element is the binder
    /// closest to the hole.
    ///
    /// [`holes`]: ExprKind::Hole
    fn replace_holes(&self, mk_pred: impl FnMut(&[List<Sort>]) -> Expr) -> Self {
        struct ReplaceHoles<F>(F, Vec<List<Sort>>);

        impl<F> TypeFolder for ReplaceHoles<F>
        where
            F: FnMut(&[List<Sort>]) -> Expr,
        {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.1.push(t.vars().to_sort_list());
                let t = t.super_fold_with(self);
                self.1.pop();
                t
            }

            fn fold_expr(&mut self, e: &Expr) -> Expr {
                if let ExprKind::Hole = e.kind() {
                    self.0(&self.1)
                } else {
                    e.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut ReplaceHoles(mk_pred, vec![]))
    }

    /// Turns each [`TyKind::Indexed`] into [`TyKind::Exists`] with a [`hole`] and replaces
    /// all existing predicates with a [`hole`].
    /// For example, `Vec<{v. i32[v] | v > 0}>[n]` becomes `{n. Vec<{v. i32[v] | *}>[n] | *}`.
    ///
    /// [`hole`]: ExprKind::Hole
    fn with_holes(&self) -> Self {
        struct WithHoles {
            in_exists: bool,
        }

        impl TypeFolder for WithHoles {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                match ty.kind() {
                    TyKind::Indexed(bty, _) => {
                        if self.in_exists {
                            ty.super_fold_with(self)
                        } else {
                            Ty::exists_with_constr(bty.fold_with(self), Expr::hole())
                        }
                    }
                    TyKind::Exists(ty) => {
                        Ty::exists(ty.fold_with(&mut WithHoles { in_exists: true }))
                    }
                    TyKind::Constr(_, ty) => Ty::constr(Expr::hole(), ty.fold_with(self)),
                    _ => ty.super_fold_with(self),
                }
            }
        }

        self.fold_with(&mut WithHoles { in_exists: false })
    }

    fn replace_evars(&self, evars: &EVarSol) -> Self {
        self.fold_with(&mut EVarSubstFolder::new(evars))
            .normalize(&Default::default())
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
                if let ReLateBound(debruijn, br) = *re && debruijn >= self.current_index {
                    ReLateBound(debruijn.shifted_in(self.amount), br)
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::LateBound(debruijn, idx)) = expr.kind()
                    && *debruijn >= self.current_index
                {
                    Expr::late_bvar(debruijn.shifted_in(self.amount), *idx)
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
                if let ReLateBound(debruijn, br) = *re && debruijn >= self.current_index {
                    ReLateBound(debruijn.shifted_out(self.amount), br)
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::LateBound(debruijn, idx)) = expr.kind()
                    && debruijn >= &self.current_index
                {
                    Expr::late_bvar(debruijn.shifted_out(self.amount), *idx)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }
}

pub trait TypeSuperFoldable: TypeFoldable {
    fn try_super_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error>;

    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.try_super_fold_with(folder).into_ok()
    }
}

impl TypeVisitable for Clause {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.kind.visit_with(visitor)
    }
}

impl TypeFoldable for Clause {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(Clause { kind: self.kind.try_fold_with(folder)? })
    }
}

impl TypeVisitable for ClauseKind {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            ClauseKind::FnTrait(pred) => pred.visit_with(visitor),
            ClauseKind::Projection(pred) => pred.visit_with(visitor),
            ClauseKind::GeneratorOblig(pred) => pred.visit_with(visitor),
        }
    }
}

impl TypeFoldable for ClauseKind {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            ClauseKind::FnTrait(pred) => Ok(ClauseKind::FnTrait(pred.try_fold_with(folder)?)),
            ClauseKind::Projection(pred) => Ok(ClauseKind::Projection(pred.try_fold_with(folder)?)),
            ClauseKind::GeneratorOblig(pred) => {
                Ok(ClauseKind::GeneratorOblig(pred.try_fold_with(folder)?))
            }
        }
    }
}

impl TypeVisitable for GeneratorObligPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.args.visit_with(visitor)?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for GeneratorObligPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(GeneratorObligPredicate {
            def_id: self.def_id,
            args: self.args.try_fold_with(folder)?,
            output: self.output.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for ProjectionPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.alias_ty.visit_with(visitor)?;
        self.term.visit_with(visitor)
    }
}

impl TypeFoldable for ProjectionPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(ProjectionPredicate {
            alias_ty: self.alias_ty.try_fold_with(folder)?,
            term: self.term.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for FnTraitPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.self_ty.visit_with(visitor)?;
        self.tupled_args.visit_with(visitor)?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for FnTraitPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(FnTraitPredicate {
            self_ty: self.self_ty.try_fold_with(folder)?,
            tupled_args: self.tupled_args.try_fold_with(folder)?,
            output: self.output.try_fold_with(folder)?,
            kind: self.kind,
        })
    }
}

impl TypeVisitable for Sort {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Sort::Tuple(sorts) | Sort::App(_, sorts) => sorts.visit_with(visitor),
            Sort::Func(fsort) => fsort.inputs_and_output.visit_with(visitor),
            Sort::Int | Sort::Bool | Sort::Real | Sort::BitVec(_) | Sort::Loc | Sort::Param(_) => {
                ControlFlow::Continue(())
            }
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
            Sort::App(ctor, sorts) => Sort::app(*ctor, sorts.try_fold_with(folder)?),
            Sort::Func(fsort) => {
                Sort::Func(FuncSort {
                    inputs_and_output: fsort.inputs_and_output.try_fold_with(folder)?,
                })
            }
            Sort::Int | Sort::Bool | Sort::Real | Sort::Loc | Sort::BitVec(_) | Sort::Param(_) => {
                self.clone()
            }
        };
        Ok(sort)
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
        self.value.visit_with(visitor)
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
        Ok(Binder::new(self.value.try_fold_with(folder)?, self.vars.try_fold_with(folder)?))
    }
}

impl TypeVisitable for BoundVariableKind {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            BoundVariableKind::Region(_) => ControlFlow::Continue(()),
            BoundVariableKind::Refine(sort, _) => sort.visit_with(visitor),
        }
    }
}

impl TypeFoldable for BoundVariableKind {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let re = match self {
            BoundVariableKind::Region(re) => BoundVariableKind::Region(*re),
            BoundVariableKind::Refine(sort, mode) => {
                BoundVariableKind::Refine(sort.try_fold_with(folder)?, *mode)
            }
        };
        Ok(re)
    }
}

impl TypeVisitable for VariantSig {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.fields
            .iter()
            .try_for_each(|ty| ty.visit_with(visitor))?;
        self.ret.visit_with(visitor)
    }
}

impl TypeFoldable for VariantSig {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let fields = self
            .fields
            .iter()
            .map(|ty| ty.try_fold_with(folder))
            .try_collect()?;
        let ret = self.ret.try_fold_with(folder)?;
        Ok(VariantSig::new(fields, ret))
    }
}

impl<T: TypeVisitable> TypeVisitable for Opaqueness<T> {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        if let Opaqueness::Transparent(t) = self {
            t.visit_with(visitor)
        } else {
            ControlFlow::Continue(())
        }
    }
}

impl<T: TypeFoldable> TypeFoldable for Opaqueness<T> {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        self.as_ref().map(|t| t.try_fold_with(folder)).transpose()
    }
}

impl TypeVisitable for FnSig {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.requires
            .iter()
            .try_for_each(|constr| constr.visit_with(visitor))?;
        self.args
            .iter()
            .try_for_each(|arg| arg.visit_with(visitor))?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for FnSig {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let requires = self.requires.try_fold_with(folder)?;
        let args = self.args.try_fold_with(folder)?;
        let output = self.output.try_fold_with(folder)?;
        Ok(FnSig::new(requires, args, output))
    }
}

impl TypeVisitable for FnOutput {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.ret.visit_with(visitor)?;
        self.ensures.visit_with(visitor)
    }
}

impl TypeFoldable for FnOutput {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(FnOutput::new(self.ret.try_fold_with(folder)?, self.ensures.try_fold_with(folder)?))
    }
}

impl TypeVisitable for Constraint {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self {
            Constraint::Type(path, ty) => {
                path.to_expr().visit_with(visitor)?;
                ty.visit_with(visitor)
            }
            Constraint::Pred(e) => e.visit_with(visitor),
        }
    }
}

impl TypeFoldable for Constraint {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let c = match self {
            Constraint::Type(path, ty) => {
                let path_expr = path
                    .to_expr()
                    .try_fold_with(folder)?
                    .normalize(&Default::default());
                Constraint::Type(
                    path_expr.to_path().unwrap_or_else(|| {
                        bug!("invalid path `{path_expr:?}` produced when folding `{self:?}`",)
                    }),
                    ty.try_fold_with(folder)?,
                )
            }
            Constraint::Pred(e) => Constraint::Pred(e.try_fold_with(folder)?),
        };
        Ok(c)
    }
}

impl TypeVisitable for Ty {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        visitor.visit_ty(self)
    }
}

impl TypeSuperVisitable for Ty {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                bty.visit_with(visitor)?;
                idxs.visit_with(visitor)
            }
            TyKind::Exists(exists) => exists.visit_with(visitor),
            TyKind::Ptr(_, path) => path.to_expr().visit_with(visitor),
            TyKind::Constr(pred, ty) => {
                pred.visit_with(visitor)?;
                ty.visit_with(visitor)
            }
            TyKind::Downcast(.., substs, _, fields) => {
                substs.visit_with(visitor)?;
                fields.visit_with(visitor)
            }
            TyKind::Blocked(ty) => ty.visit_with(visitor),
            TyKind::Param(_) | TyKind::Discr(..) | TyKind::Uninit => ControlFlow::Continue(()),
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
            TyKind::Ptr(pk, path) => {
                let pk = match pk {
                    PtrKind::Shr(re) => PtrKind::Shr(re.try_fold_with(folder)?),
                    PtrKind::Mut(re) => PtrKind::Mut(re.try_fold_with(folder)?),
                    PtrKind::Box => PtrKind::Box,
                };
                Ty::ptr(
                    pk,
                    path.to_expr()
                        .try_fold_with(folder)?
                        .normalize(&Default::default())
                        .to_path()
                        .expect("type folding produced an invalid path"),
                )
            }
            TyKind::Constr(pred, ty) => {
                Ty::constr(pred.try_fold_with(folder)?, ty.try_fold_with(folder)?)
            }
            TyKind::Downcast(adt, substs, ty, variant, fields) => {
                Ty::downcast(
                    adt.clone(),
                    substs.clone(),
                    ty.clone(),
                    *variant,
                    fields.try_fold_with(folder)?,
                )
            }
            TyKind::Blocked(ty) => Ty::blocked(ty.try_fold_with(folder)?),
            TyKind::Param(_) | TyKind::Uninit | TyKind::Discr(..) => self.clone(),
        };
        Ok(ty)
    }
}

impl TypeVisitable for Region {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        ControlFlow::Continue(())
    }
}

impl TypeFoldable for Region {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_region(self)
    }
}

impl TypeVisitable for Index {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.expr.visit_with(visitor)
    }
}

impl TypeFoldable for Index {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(Index { expr: self.expr.try_fold_with(folder)?, is_binder: self.is_binder.clone() })
    }
}

impl TypeVisitable for BaseTy {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        visitor.visit_bty(self)
    }
}

impl TypeSuperVisitable for BaseTy {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self {
            BaseTy::Adt(_, substs) => substs.iter().try_for_each(|ty| ty.visit_with(visitor)),
            BaseTy::Slice(ty) => ty.visit_with(visitor),
            BaseTy::RawPtr(ty, _) => ty.visit_with(visitor),
            BaseTy::Ref(_, ty, _) => ty.visit_with(visitor),
            BaseTy::Tuple(tys) => tys.iter().try_for_each(|ty| ty.visit_with(visitor)),
            BaseTy::Array(ty, _) => ty.visit_with(visitor),
            BaseTy::Alias(_, alias_ty) => alias_ty.visit_with(visitor),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Closure(_, _)
            | BaseTy::Generator(_, _)
            | BaseTy::GeneratorWitness(_)
            | BaseTy::Never
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
            BaseTy::Adt(adt_def, substs) => {
                BaseTy::adt(adt_def.clone(), substs.try_fold_with(folder)?)
            }
            BaseTy::Slice(ty) => BaseTy::Slice(ty.try_fold_with(folder)?),
            BaseTy::RawPtr(ty, mu) => BaseTy::RawPtr(ty.try_fold_with(folder)?, *mu),
            BaseTy::Ref(re, ty, mutbl) => {
                BaseTy::Ref(re.try_fold_with(folder)?, ty.try_fold_with(folder)?, *mutbl)
            }
            BaseTy::Tuple(tys) => BaseTy::Tuple(tys.try_fold_with(folder)?),
            BaseTy::Array(ty, c) => BaseTy::Array(ty.try_fold_with(folder)?, c.clone()),
            BaseTy::Alias(kind, alias_ty) => BaseTy::Alias(*kind, alias_ty.try_fold_with(folder)?),
            BaseTy::Int(_)
            | BaseTy::Param(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Never => self.clone(),
            BaseTy::Closure(did, substs) => BaseTy::Closure(*did, substs.try_fold_with(folder)?),
            BaseTy::Generator(did, substs) => {
                BaseTy::Generator(*did, substs.try_fold_with(folder)?)
            }
            BaseTy::GeneratorWitness(args) => BaseTy::GeneratorWitness(args.try_fold_with(folder)?),
        };
        Ok(bty)
    }
}

impl TypeVisitable for AliasTy {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.args.visit_with(visitor)
    }
}

impl TypeFoldable for AliasTy {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(AliasTy { args: self.args.try_fold_with(folder)?, def_id: self.def_id })
    }
}

impl TypeVisitable for GenericArg {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self {
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::BaseTy(ty) => ty.visit_with(visitor),
            GenericArg::Lifetime(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for GenericArg {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let arg = match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.try_fold_with(folder)?),
            GenericArg::BaseTy(ty) => GenericArg::BaseTy(ty.try_fold_with(folder)?),
            GenericArg::Lifetime(re) => GenericArg::Lifetime(re.try_fold_with(folder)?),
        };
        Ok(arg)
    }
}

impl TypeVisitable for KVar {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.args.visit_with(visitor)
    }
}

impl TypeFoldable for KVar {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(KVar {
            kvid: self.kvid,
            self_args: self.self_args,
            args: self.args.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for Expr {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        visitor.visit_expr(self)
    }
}

impl TypeSuperVisitable for Expr {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self.kind() {
            ExprKind::Var(var) => var.visit_with(visitor),
            ExprKind::BinaryOp(_, e1, e2) => {
                e1.visit_with(visitor)?;
                e2.visit_with(visitor)
            }
            ExprKind::Tuple(exprs) => exprs.iter().try_for_each(|e| e.visit_with(visitor)),
            ExprKind::PathProj(e, _) | ExprKind::UnaryOp(_, e) | ExprKind::TupleProj(e, _) => {
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
            ExprKind::Abs(body) => body.visit_with(visitor),
            ExprKind::Constant(_)
            | ExprKind::Hole
            | ExprKind::Local(_)
            | ExprKind::GlobalFunc(..)
            | ExprKind::ConstDefId(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeVisitable for Var {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self {
            Var::Free(name) => visitor.visit_fvar(*name),
            Var::LateBound(_, _) | Var::EarlyBound(_) | Var::EVar(_) => ControlFlow::Continue(()),
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
            ExprKind::Var(var) => Expr::var(*var, span),
            ExprKind::Local(local) => Expr::local(*local, span),
            ExprKind::Constant(c) => Expr::constant_at(*c, span),
            ExprKind::ConstDefId(did) => Expr::const_def_id(*did, span),
            ExprKind::BinaryOp(op, e1, e2) => {
                Expr::binary_op(*op, e1.try_fold_with(folder)?, e2.try_fold_with(folder)?, span)
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.try_fold_with(folder)?, span),
            ExprKind::TupleProj(e, proj) => Expr::tuple_proj(e.try_fold_with(folder)?, *proj, span),
            ExprKind::Tuple(exprs) => {
                let exprs = exprs
                    .iter()
                    .map(|e| e.try_fold_with(folder))
                    .try_collect_vec()?;
                Expr::tuple(exprs)
            }
            ExprKind::PathProj(e, field) => Expr::path_proj(e.try_fold_with(folder)?, *field),
            ExprKind::App(func, arg) => {
                Expr::app(func.try_fold_with(folder)?, arg.try_fold_with(folder)?, span)
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                Expr::ite(
                    p.try_fold_with(folder)?,
                    e1.try_fold_with(folder)?,
                    e2.try_fold_with(folder)?,
                    span,
                )
            }
            ExprKind::Hole => Expr::hole(),
            ExprKind::KVar(kvar) => Expr::kvar(kvar.try_fold_with(folder)?),
            ExprKind::Abs(body) => Expr::abs(body.try_fold_with(folder)?),
            ExprKind::GlobalFunc(func, kind) => Expr::global_func(*func, *kind),
        };
        Ok(expr)
    }
}

impl<T> TypeVisitable for List<T>
where
    T: TypeVisitable,
    [T]: Internable,
{
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.iter().try_for_each(|t| t.visit_with(visitor))
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

impl TypeVisitable for Qualifier {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.body.visit_with(visitor)
    }
}

impl TypeFoldable for Qualifier {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(Qualifier {
            name: self.name,
            body: self.body.try_fold_with(folder)?,
            global: self.global,
        })
    }
}

impl TypeVisitable for Invariant {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        self.pred.visit_with(visitor)
    }
}

impl TypeFoldable for Invariant {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let pred = self.pred.try_fold_with(folder)?;
        Ok(Invariant { pred })
    }
}
