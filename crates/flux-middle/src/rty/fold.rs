//! This modules folows the implementation of folding in rustc. For more information read the
//! documentation in [`rustc_middle::ty::fold`].

use std::ops::ControlFlow;

use flux_arc_interner::{Internable, List};
use flux_common::bug;
use itertools::Itertools;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{
    evars::EVarSol,
    normalize::{Normalizer, SpecFuncDefns},
    projections,
    subst::EVarSubstFolder,
    AliasReft, AliasTy, BaseTy, BinOp, Binder, BoundVariableKind, Clause, ClauseKind, Const,
    CoroutineObligPredicate, Ensures, ExistentialPredicate, ExistentialProjection,
    ExistentialTraitRef, Expr, ExprKind, FnOutput, FnSig, FnTraitPredicate, FuncSort, GenericArg,
    Invariant, KVar, Lambda, Name, Opaqueness, OutlivesPredicate, PolyFuncSort,
    ProjectionPredicate, PtrKind, Qualifier, ReBound, ReErased, Region, Sort, SortArg, SubsetTy,
    TraitPredicate, TraitRef, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{expr::HoleKind, BoundVariableKindsExt, Var, VariantSig},
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
}

pub trait TypeSuperVisitable: TypeVisitable {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy>;
}

pub trait TypeFoldable: TypeVisitable {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error>;

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.try_fold_with(folder).into_ok()
    }

    fn normalize_projections<'tcx>(
        &self,
        genv: GlobalEnv<'_, 'tcx>,
        infcx: &rustc_infer::infer::InferCtxt<'tcx>,
        callsite_def_id: DefId,
    ) -> QueryResult<Self> {
        let mut normalizer = projections::Normalizer::new(genv, infcx, callsite_def_id)?;
        self.erase_regions().try_fold_with(&mut normalizer)
    }

    /// Normalize expressions by applying beta reductions for tuples and lambda abstractions.
    fn normalize(&self, defns: &SpecFuncDefns) -> Self {
        self.fold_with(&mut Normalizer::new(defns))
    }

    /// Replaces all [holes] with the result of calling a closure. The closure takes a list with
    /// all the *layers* of [bound] variables at the point the hole was found. Each layer corresponds
    /// to the list of sorts bound at that level. The list is ordered from outermost to innermost
    /// binder, i.e., the last element is the binder closest to the hole.
    ///
    /// [holes]: ExprKind::Hole
    /// [bound]: Binder
    fn replace_holes(&self, f: impl FnMut(&[List<Sort>], HoleKind) -> Expr) -> Self {
        struct ReplaceHoles<F>(F, Vec<List<Sort>>);

        impl<F> TypeFolder for ReplaceHoles<F>
        where
            F: FnMut(&[List<Sort>], HoleKind) -> Expr,
        {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.1.push(t.vars().to_sort_list());
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
        }

        self.fold_with(&mut WithHoles)
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
            ClauseKind::Trait(pred) => pred.visit_with(visitor),
            ClauseKind::Projection(pred) => pred.visit_with(visitor),
            ClauseKind::CoroutineOblig(pred) => pred.visit_with(visitor),
            ClauseKind::TypeOutlives(pred) => pred.visit_with(visitor),
            ClauseKind::ConstArgHasType(_const, ty) => ty.visit_with(visitor),
        }
    }
}

impl TypeFoldable for ClauseKind {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            ClauseKind::FnTrait(pred) => Ok(ClauseKind::FnTrait(pred.try_fold_with(folder)?)),
            ClauseKind::Trait(pred) => Ok(ClauseKind::Trait(pred.try_fold_with(folder)?)),
            ClauseKind::Projection(pred) => Ok(ClauseKind::Projection(pred.try_fold_with(folder)?)),
            ClauseKind::CoroutineOblig(pred) => {
                Ok(ClauseKind::CoroutineOblig(pred.try_fold_with(folder)?))
            }
            ClauseKind::TypeOutlives(pred) => {
                Ok(ClauseKind::TypeOutlives(pred.try_fold_with(folder)?))
            }
            ClauseKind::ConstArgHasType(const_, ty) => {
                Ok(ClauseKind::ConstArgHasType(const_.clone(), ty.try_fold_with(folder)?))
            }
        }
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

impl TypeVisitable for TraitPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.trait_ref.visit_with(visitor)
    }
}

impl TypeFoldable for TraitPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(TraitPredicate { trait_ref: self.trait_ref.try_fold_with(folder)? })
    }
}

impl TypeVisitable for TraitRef {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.args.visit_with(visitor)
    }
}

impl TypeFoldable for TraitRef {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(TraitRef { def_id: self.def_id, args: self.args.try_fold_with(folder)? })
    }
}

impl TypeVisitable for ExistentialTraitRef {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.args.visit_with(visitor)
    }
}

impl TypeFoldable for ExistentialTraitRef {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(ExistentialTraitRef { def_id: self.def_id, args: self.args.try_fold_with(folder)? })
    }
}

impl TypeVisitable for ExistentialProjection {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.args.visit_with(visitor)?;
        self.term.visit_with(visitor)
    }
}

impl TypeFoldable for ExistentialProjection {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(ExistentialProjection {
            def_id: self.def_id,
            args: self.args.try_fold_with(folder)?,
            term: self.term.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for ExistentialPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            ExistentialPredicate::Trait(trait_ref) => trait_ref.visit_with(visitor),
            ExistentialPredicate::Projection(projection) => projection.visit_with(visitor),
            ExistentialPredicate::AutoTrait(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for ExistentialPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            ExistentialPredicate::Trait(trait_ref) => {
                Ok(ExistentialPredicate::Trait(trait_ref.try_fold_with(folder)?))
            }
            ExistentialPredicate::Projection(projection) => {
                Ok(ExistentialPredicate::Projection(projection.try_fold_with(folder)?))
            }
            ExistentialPredicate::AutoTrait(def_id) => Ok(ExistentialPredicate::AutoTrait(*def_id)),
        }
    }
}

impl TypeVisitable for CoroutineObligPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.upvar_tys.visit_with(visitor)?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for CoroutineObligPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(CoroutineObligPredicate {
            def_id: self.def_id,
            resume_ty: self.resume_ty.try_fold_with(folder)?,
            upvar_tys: self.upvar_tys.try_fold_with(folder)?,
            output: self.output.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for ProjectionPredicate {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.projection_ty.visit_with(visitor)?;
        self.term.visit_with(visitor)
    }
}

impl TypeFoldable for ProjectionPredicate {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(ProjectionPredicate {
            projection_ty: self.projection_ty.try_fold_with(folder)?,
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

impl TypeVisitable for SortArg {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            SortArg::Sort(sort) => sort.visit_with(visitor),
            SortArg::BvSize(_) => ControlFlow::Continue(()),
        }
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
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::Str
            | Sort::BitVec(_)
            | Sort::Loc
            | Sort::Param(_)
            | Sort::Var(_)
            | Sort::Infer(_)
            | Sort::Err => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for SortArg {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            SortArg::Sort(sort) => Ok(SortArg::Sort(sort.try_fold_with(folder)?)),
            SortArg::BvSize(size) => Ok(SortArg::BvSize(*size)),
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
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::Loc
            | Sort::Str
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

impl TypeVisitable for FuncSort {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.inputs_and_output.visit_with(visitor)
    }
}

impl TypeFoldable for FuncSort {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(FuncSort { inputs_and_output: self.inputs_and_output.try_fold_with(folder)? })
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
            BoundVariableKind::Refine(sort, ..) => sort.visit_with(visitor),
        }
    }
}

impl TypeFoldable for BoundVariableKind {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let re = match self {
            BoundVariableKind::Region(re) => BoundVariableKind::Region(*re),
            BoundVariableKind::Refine(sort, mode, kind) => {
                BoundVariableKind::Refine(sort.try_fold_with(folder)?, *mode, *kind)
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
        self.idx.visit_with(visitor)
    }
}

impl TypeFoldable for VariantSig {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let args = self.args.try_fold_with(folder)?;
        let fields = self.fields.try_fold_with(folder)?;
        let idx = self.idx.try_fold_with(folder)?;
        Ok(VariantSig::new(self.adt_def.clone(), args, fields, idx))
    }
}

impl<T: TypeVisitable> TypeVisitable for Opaqueness<T> {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
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

impl<T: TypeVisitable> TypeVisitable for Vec<T> {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.iter().try_for_each(|t| t.visit_with(visitor))
    }
}

impl TypeVisitable for FnSig {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.requires
            .iter()
            .try_for_each(|constr| constr.visit_with(visitor))?;
        self.inputs
            .iter()
            .try_for_each(|arg| arg.visit_with(visitor))?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for FnSig {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let requires = self.requires.try_fold_with(folder)?;
        let args = self.inputs.try_fold_with(folder)?;
        let output = self.output.try_fold_with(folder)?;
        Ok(FnSig::new(self.safety, self.abi, requires, args, output))
    }
}

impl TypeVisitable for FnOutput {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.ret.visit_with(visitor)?;
        self.ensures.visit_with(visitor)
    }
}

impl TypeFoldable for FnOutput {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(FnOutput::new(self.ret.try_fold_with(folder)?, self.ensures.try_fold_with(folder)?))
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
                let path_expr = path
                    .to_expr()
                    .try_fold_with(folder)?
                    .normalize(&Default::default());
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

impl TypeVisitable for AliasReft {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.args.visit_with(visitor)
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
            TyKind::Alias(_, alias_ty) => alias_ty.visit_with(visitor),
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
                        .normalize(&Default::default())
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
                        .normalize(&Default::default())
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
            TyKind::Alias(kind, alias_ty) => Ty::alias(*kind, alias_ty.try_fold_with(folder)?),
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

impl TypeSuperFoldable for Const {
    fn try_super_fold_with<F: FallibleTypeFolder>(
        &self,
        _folder: &mut F,
    ) -> Result<Self, F::Error> {
        // FIXME(nilehmann) we are not folding the type in `ConstKind::Value` because is a rustc::ty::Ty
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

impl TypeFoldable for Region {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_region(self)
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
            BaseTy::Slice(ty) => ty.visit_with(visitor),
            BaseTy::RawPtr(ty, _) => ty.visit_with(visitor),
            BaseTy::Ref(_, ty, _) => ty.visit_with(visitor),
            BaseTy::FnPtr(poly_fn_sig) => poly_fn_sig.visit_with(visitor),
            BaseTy::Tuple(tys) => tys.visit_with(visitor),
            BaseTy::Array(ty, _) => ty.visit_with(visitor),
            BaseTy::Coroutine(_, resume_ty, upvars) => {
                resume_ty.visit_with(visitor)?;
                upvars.visit_with(visitor)
            }
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Closure(_, _)
            | BaseTy::Never
            | BaseTy::Param(_) => ControlFlow::Continue(()),
            BaseTy::Dynamic(exi_preds, _) => exi_preds.visit_with(visitor),
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
            BaseTy::Slice(ty) => BaseTy::Slice(ty.try_fold_with(folder)?),
            BaseTy::RawPtr(ty, mu) => BaseTy::RawPtr(ty.try_fold_with(folder)?, *mu),
            BaseTy::Ref(re, ty, mutbl) => {
                BaseTy::Ref(re.try_fold_with(folder)?, ty.try_fold_with(folder)?, *mutbl)
            }
            BaseTy::FnPtr(decl) => BaseTy::FnPtr(decl.try_fold_with(folder)?),
            BaseTy::Tuple(tys) => BaseTy::Tuple(tys.try_fold_with(folder)?),
            BaseTy::Array(ty, c) => {
                BaseTy::Array(ty.try_fold_with(folder)?, c.try_fold_with(folder)?)
            }
            BaseTy::Int(_)
            | BaseTy::Param(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Never => self.clone(),
            BaseTy::Closure(did, args) => BaseTy::Closure(*did, args.try_fold_with(folder)?),
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
        };
        Ok(bty)
    }
}

impl TypeVisitable for AliasTy {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.args.visit_with(visitor)
    }
}

impl TypeFoldable for AliasTy {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(AliasTy {
            args: self.args.try_fold_with(folder)?,
            def_id: self.def_id,
            refine_args: self.refine_args.try_fold_with(folder)?,
        })
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
            GenericArg::Base(sty) => GenericArg::Base(sty.try_fold_with(folder)?),
            GenericArg::Lifetime(re) => GenericArg::Lifetime(re.try_fold_with(folder)?),
            GenericArg::Const(c) => GenericArg::Const(c.try_fold_with(folder)?),
        };
        Ok(arg)
    }
}

impl TypeVisitable for KVar {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
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
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        visitor.visit_expr(self)
    }
}

impl TypeSuperVisitable for Expr {
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self.kind() {
            ExprKind::Var(var) => var.visit_with(visitor),
            ExprKind::BinaryOp(_, e1, e2) => {
                e1.visit_with(visitor)?;
                e2.visit_with(visitor)
            }
            ExprKind::Aggregate(_, flds) => flds.visit_with(visitor),
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
            ExprKind::Alias(alias, args) => {
                alias.visit_with(visitor)?;
                args.visit_with(visitor)
            }
            ExprKind::Abs(body) => body.visit_with(visitor),
            ExprKind::ForAll(expr) => expr.visit_with(visitor),
            ExprKind::Constant(_)
            | ExprKind::Hole(_)
            | ExprKind::Local(_)
            | ExprKind::GlobalFunc(..)
            | ExprKind::ConstDefId(_) => ControlFlow::Continue(()),
        }
    }
}

impl TypeVisitable for Lambda {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.body.visit_with(visitor)?;
        self.output.visit_with(visitor)
    }
}

impl TypeFoldable for Lambda {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(Lambda {
            body: self.body.try_fold_with(folder)?,
            output: self.output.try_fold_with(folder)?,
        })
    }
}

impl TypeVisitable for Var {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Var::Free(name) => visitor.visit_fvar(*name),
            Var::ConstGeneric(_) | Var::Bound(_, _) | Var::EarlyParam(_) | Var::EVar(_) => {
                ControlFlow::Continue(())
            }
        }
    }
}

impl TypeFoldable for AliasReft {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let trait_id = self.trait_id;
        let args = self.args.try_fold_with(folder)?;
        Ok(AliasReft { trait_id, name: self.name, args })
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
            ExprKind::Aggregate(kind, flds) => {
                let flds = flds.iter().map(|e| e.try_fold_with(folder)).try_collect()?;
                Expr::aggregate(*kind, flds)
            }
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
            ExprKind::Abs(lam) => Expr::abs(lam.try_fold_with(folder)?),
            ExprKind::GlobalFunc(func, kind) => Expr::global_func(*func, *kind),
            ExprKind::Alias(alias, args) => {
                let alias = alias.try_fold_with(folder)?;
                let args = args.try_fold_with(folder)?;
                Expr::alias(alias, args)
            }
            ExprKind::ForAll(expr) => Expr::forall(expr.try_fold_with(folder)?),
        };
        Ok(expr.at_opt(span))
    }
}

impl TypeVisitable for BinOp {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            BinOp::Gt(sort) | BinOp::Ge(sort) | BinOp::Lt(sort) | BinOp::Le(sort) => {
                sort.visit_with(visitor)
            }
            BinOp::Iff
            | BinOp::Imp
            | BinOp::Or
            | BinOp::And
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod => ControlFlow::Continue(()),
        }
    }
}

impl TypeFoldable for BinOp {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let op = match self {
            BinOp::Iff => BinOp::Iff,
            BinOp::Imp => BinOp::Imp,
            BinOp::Or => BinOp::Or,
            BinOp::And => BinOp::And,
            BinOp::Eq => BinOp::Eq,
            BinOp::Ne => BinOp::Ne,
            BinOp::Gt(sort) => BinOp::Gt(sort.try_fold_with(folder)?),
            BinOp::Ge(sort) => BinOp::Ge(sort.try_fold_with(folder)?),
            BinOp::Lt(sort) => BinOp::Lt(sort.try_fold_with(folder)?),
            BinOp::Le(sort) => BinOp::Le(sort.try_fold_with(folder)?),
            BinOp::Add => BinOp::Add,
            BinOp::Sub => BinOp::Sub,
            BinOp::Mul => BinOp::Mul,
            BinOp::Div => BinOp::Div,
            BinOp::Mod => BinOp::Mod,
        };
        Ok(op)
    }
}

impl TypeVisitable for HoleKind {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            HoleKind::Pred => ControlFlow::Continue(()),
            HoleKind::Expr(sort) => sort.visit_with(visitor),
        }
    }
}

impl TypeFoldable for HoleKind {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            HoleKind::Pred => Ok(HoleKind::Pred),
            HoleKind::Expr(sort) => Ok(HoleKind::Expr(sort.try_fold_with(folder)?)),
        }
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
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
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
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        self.pred.visit_with(visitor)
    }
}

impl TypeFoldable for Invariant {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let pred = self.pred.try_fold_with(folder)?;
        Ok(Invariant { pred })
    }
}

pub struct BottomUpFolder<F, G, H>
where
    F: FnMut(Ty) -> Ty,
    G: FnMut(Region) -> Region,
    H: FnMut(Const) -> Const,
{
    pub ty_op: F,
    pub lt_op: G,
    pub ct_op: H,
}

impl<F, G, H> TypeFolder for BottomUpFolder<F, G, H>
where
    F: FnMut(Ty) -> Ty,
    G: FnMut(Region) -> Region,
    H: FnMut(Const) -> Const,
{
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        let t = ty.super_fold_with(self);
        (self.ty_op)(t)
    }

    fn fold_region(&mut self, r: &Region) -> Region {
        // This one is a little different, because `super_fold_with` is not
        // implemented on non-recursive `Region`.
        (self.lt_op)(*r)
    }

    fn fold_const(&mut self, ct: &Const) -> Const {
        let ct = ct.super_fold_with(self);
        (self.ct_op)(ct)
    }
}
