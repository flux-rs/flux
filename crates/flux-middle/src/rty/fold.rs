//! This modules follows the implementation of folding in rustc. For more information read the
//! documentation in `rustc_type_ir::fold`.

use std::ops::ControlFlow;

use flux_arc_interner::{Internable, List};
use flux_common::bug;
use itertools::Itertools;
use rustc_data_structures::fx::FxHashMap;
use rustc_hash::FxHashSet;
use rustc_type_ir::{BoundVar, DebruijnIndex, INNERMOST};

use super::{
    BaseTy, Binder, BoundVariableKinds, Const, EVid, EarlyReftParam, Ensures, Expr, ExprKind,
    GenericArg, Name, OutlivesPredicate, PolyFuncSort, PtrKind, ReBound, ReErased, Region, Sort,
    SubsetTy, Ty, TyKind, TyOrBase, normalize::Normalizer,
};
use crate::{
    global_env::GlobalEnv,
    rty::{BoundReft, BoundRegion, Var, VariantSig, expr::HoleKind},
};

pub trait TypeVisitor: Sized {
    type BreakTy = !;

    fn enter_binder(&mut self, _vars: &BoundVariableKinds) {}

    fn exit_binder(&mut self) {}

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

    fn try_enter_binder(&mut self, _vars: &BoundVariableKinds) {}

    fn try_exit_binder(&mut self) {}

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
    fn enter_binder(&mut self, _vars: &BoundVariableKinds) {}

    fn exit_binder(&mut self) {}

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

    fn try_enter_binder(&mut self, vars: &BoundVariableKinds) {
        self.enter_binder(vars);
    }

    fn try_exit_binder(&mut self) {
        self.exit_binder();
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

            fn enter_binder(&mut self, _: &BoundVariableKinds) {
                self.outer_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.outer_index.shift_out(1);
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
        let _ = self.visit_with(&mut collector);
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
        let _ = self.visit_with(&mut collector);
        collector.0
    }

    /// Gives the indices of the provided bvars which:
    ///   1. Only occur a single time.
    ///   2. In their occurrence, are either
    ///      a. The direct argument in an index (e.g. `exists b0. usize[b0]`)
    ///      b. The direct argument of a constructor in an index (e.g.
    ///      `exists b0. Vec<usize>[{len: b0}]`)
    ///
    /// This is to be used for "re-sugaring" existentials into surface syntax
    /// that doesn't use existentials.
    ///
    /// For 2b., we do need to be careful to ensure that if a constructor has
    /// multiple arguments, they _all_ are redundant bvars, e.g. as in
    ///
    ///     exists b0, b1. RMat<f32>[{rows: b0, cols: b1}]
    ///
    /// which may be rewritten as `RMat<f32>`,
    /// versus the (unlikely) edge case
    ///
    ///     exists b0. RMat<f32>[{rows: b0, cols: b0}]
    ///
    /// for which the existential is now necessary.
    ///
    /// NOTE: this only applies to refinement bvars.
    fn redundant_bvars(&self) -> FxHashSet<BoundVar> {
        struct RedundantBVarFinder {
            current_index: DebruijnIndex,
            total_bvar_occurrences: FxHashMap<BoundVar, usize>,
            bvars_appearing_in_index: FxHashSet<BoundVar>,
        }

        impl TypeVisitor for RedundantBVarFinder {
            // Here we count all times we see a bvar
            fn visit_expr(&mut self, e: &Expr) -> ControlFlow<Self::BreakTy> {
                if let ExprKind::Var(Var::Bound(debruijn, BoundReft { var, .. })) = e.kind()
                    && debruijn == &self.current_index
                {
                    self.total_bvar_occurrences
                        .entry(*var)
                        .and_modify(|count| {
                            *count += 1;
                        })
                        .or_insert(1);
                }
                e.super_visit_with(self)
            }

            fn visit_ty(&mut self, ty: &Ty) -> ControlFlow<Self::BreakTy> {
                // Here we check for bvars specifically as the direct arguments
                // to an index or as the direct arguments to a Ctor in an index.
                if let TyKind::Indexed(_bty, expr) = ty.kind() {
                    match expr.kind() {
                        ExprKind::Var(Var::Bound(debruijn, BoundReft { var, .. })) => {
                            if debruijn == &self.current_index {
                                self.bvars_appearing_in_index.insert(*var);
                            }
                        }
                        ExprKind::Ctor(_ctor, exprs) => {
                            exprs.iter().for_each(|expr| {
                                if let ExprKind::Var(Var::Bound(debruijn, BoundReft { var, .. })) =
                                    expr.kind()
                                    && debruijn == &self.current_index
                                {
                                    self.bvars_appearing_in_index.insert(*var);
                                }
                            });
                        }
                        _ => {}
                    }
                }
                ty.super_visit_with(self)
            }

            fn enter_binder(&mut self, _: &BoundVariableKinds) {
                self.current_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.current_index.shift_out(1);
            }
        }

        let mut finder = RedundantBVarFinder {
            current_index: INNERMOST,
            total_bvar_occurrences: FxHashMap::default(),
            bvars_appearing_in_index: FxHashSet::default(),
        };
        let _ = self.visit_with(&mut finder);

        finder
            .bvars_appearing_in_index
            .into_iter()
            .filter(|var_index| finder.total_bvar_occurrences.get(var_index) == Some(&1))
            .collect()
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
            fn enter_binder(&mut self, vars: &BoundVariableKinds) {
                self.1.push(vars.clone());
            }

            fn exit_binder(&mut self) {
                self.1.pop();
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

    /// Shift the [`BoundVar`] of all the the variables at index [`INNERMOST`] "horizontally" to the
    /// right by the specified `amount`.
    fn shift_horizontally(&self, amount: usize) -> Self {
        struct Shifter {
            current_index: DebruijnIndex,
            amount: usize,
        }

        impl TypeFolder for Shifter {
            fn enter_binder(&mut self, _: &BoundVariableKinds) {
                self.current_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.current_index.shift_out(1);
            }

            fn fold_region(&mut self, re: &Region) -> Region {
                if let ReBound(debruijn, br) = *re
                    && debruijn == self.current_index
                {
                    ReBound(debruijn, BoundRegion { var: br.var + self.amount, kind: br.kind })
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::Bound(debruijn, breft)) = expr.kind()
                    && debruijn == &self.current_index
                {
                    Expr::bvar(*debruijn, breft.var + self.amount, breft.kind)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }

    fn shift_in_escaping(&self, amount: u32) -> Self {
        struct Shifter {
            current_index: DebruijnIndex,
            amount: u32,
        }

        impl TypeFolder for Shifter {
            fn enter_binder(&mut self, _: &BoundVariableKinds) {
                self.current_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.current_index.shift_out(1);
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
            fn enter_binder(&mut self, _: &BoundVariableKinds) {
                self.current_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.current_index.shift_out(1);
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
        self.vars().visit_with(visitor)?;
        visitor.enter_binder(self.vars());
        self.skip_binder_ref().visit_with(visitor)?;
        visitor.exit_binder();
        ControlFlow::Continue(())
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
        let vars = self.vars().try_fold_with(folder)?;
        folder.try_enter_binder(&vars);
        let r = self.skip_binder_ref().try_fold_with(folder)?;
        folder.try_exit_binder();
        Ok(Binder::bind_with_vars(r, vars))
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

impl TypeVisitable for super::TyOrBase {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy> {
        match self {
            Self::Ty(ty) => ty.visit_with(visitor),
            Self::Base(bty) => bty.visit_with(visitor),
        }
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
            BaseTy::RawPtrMetadata(ty) => ty.visit_with(visitor),
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
            BaseTy::RawPtrMetadata(ty) => BaseTy::RawPtrMetadata(ty.try_fold_with(folder)?),
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
impl TypeFoldable for TyOrBase {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        match self {
            Self::Ty(ty) => Ok(Self::Ty(ty.try_fold_with(folder)?)),
            Self::Base(bty) => Ok(Self::Base(bty.try_fold_with(folder)?)),
        }
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
            ExprKind::IsCtor(_, _, e) => e.visit_with(visitor),
            ExprKind::FieldProj(e, _) | ExprKind::PathProj(e, _) | ExprKind::UnaryOp(_, e) => {
                e.visit_with(visitor)
            }
            ExprKind::App(func, sorts, arg) => {
                func.visit_with(visitor)?;
                sorts.visit_with(visitor)?;
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
            ExprKind::BoundedQuant(_, _, body) => body.visit_with(visitor),
            ExprKind::ForAll(expr) => expr.visit_with(visitor),
            ExprKind::Exists(expr) => expr.visit_with(visitor),
            ExprKind::Let(init, body) => {
                init.visit_with(visitor)?;
                body.visit_with(visitor)
            }
            ExprKind::Constant(_)
            | ExprKind::Hole(_)
            | ExprKind::Local(_)
            | ExprKind::GlobalFunc(..)
            | ExprKind::InternalFunc(..)
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
            ExprKind::IsCtor(def_id, variant_idx, e) => {
                Expr::is_ctor(*def_id, *variant_idx, e.try_fold_with(folder)?)
            }
            ExprKind::PathProj(e, field) => Expr::path_proj(e.try_fold_with(folder)?, *field),
            ExprKind::App(func, sorts, arg) => {
                Expr::app(
                    func.try_fold_with(folder)?,
                    sorts.try_fold_with(folder)?,
                    arg.try_fold_with(folder)?,
                )
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
            ExprKind::BoundedQuant(kind, rng, body) => {
                Expr::bounded_quant(*kind, *rng, body.try_fold_with(folder)?)
            }
            ExprKind::GlobalFunc(kind) => Expr::global_func(kind.clone()),
            ExprKind::InternalFunc(kind) => Expr::internal_func(kind.clone()),
            ExprKind::Alias(alias, args) => {
                Expr::alias(alias.try_fold_with(folder)?, args.try_fold_with(folder)?)
            }
            ExprKind::ForAll(expr) => Expr::forall(expr.try_fold_with(folder)?),
            ExprKind::Exists(expr) => Expr::exists(expr.try_fold_with(folder)?),
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

impl<T> TypeFoldable for List<T>
where
    T: TypeFoldable,
    [T]: Internable,
{
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        self.iter().map(|t| t.try_fold_with(folder)).try_collect()
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
    rustc_abi::ExternAbi,
    rustc_type_ir::ClosureKind,
    flux_rustc_bridge::ty::BoundRegionKind,
}
