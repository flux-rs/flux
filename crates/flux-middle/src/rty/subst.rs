use std::cmp::Ordering;

use flux_common::{bug, tracked_span_bug};
use rustc_type_ir::DebruijnIndex;

use self::fold::FallibleTypeFolder;
use super::fold::{TypeFolder, TypeSuperFoldable};
use crate::rty::*;

/// Substitution for late bound variables
pub(super) struct BoundVarReplacer<D> {
    current_index: DebruijnIndex,
    delegate: D,
}

pub trait BoundVarReplacerDelegate {
    fn replace_expr(&mut self, var: BoundReft) -> Expr;
    fn replace_region(&mut self, br: BoundRegion) -> Region;
}

pub(crate) struct FnMutDelegate<F1, F2> {
    pub exprs: F1,
    pub regions: F2,
}

impl<F1, F2> FnMutDelegate<F1, F2>
where
    F1: FnMut(BoundReft) -> Expr,
    F2: FnMut(BoundRegion) -> Region,
{
    pub(crate) fn new(exprs: F1, regions: F2) -> Self {
        Self { exprs, regions }
    }
}

impl<F1, F2> BoundVarReplacerDelegate for FnMutDelegate<F1, F2>
where
    F1: FnMut(BoundReft) -> Expr,
    F2: FnMut(BoundRegion) -> Region,
{
    fn replace_expr(&mut self, var: BoundReft) -> Expr {
        (self.exprs)(var)
    }

    fn replace_region(&mut self, br: BoundRegion) -> Region {
        (self.regions)(br)
    }
}

impl<D> BoundVarReplacer<D> {
    pub(super) fn new(delegate: D) -> BoundVarReplacer<D> {
        BoundVarReplacer { delegate, current_index: INNERMOST }
    }
}

impl<D> TypeFolder for BoundVarReplacer<D>
where
    D: BoundVarReplacerDelegate,
{
    fn enter_binder(&mut self, _: &BoundVariableKinds) {
        self.current_index.shift_in(1);
    }

    fn exit_binder(&mut self) {
        self.current_index.shift_out(1);
    }

    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::Var(Var::Bound(debruijn, breft)) = e.kind() {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => Expr::bvar(*debruijn, breft.var, breft.kind),
                Ordering::Equal => {
                    self.delegate
                        .replace_expr(*breft)
                        .shift_in_escaping(self.current_index.as_u32())
                }
                Ordering::Greater => Expr::bvar(debruijn.shifted_out(1), breft.var, breft.kind),
            }
        } else {
            e.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        if let ReBound(debruijn, br) = *re {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => *re,
                Ordering::Equal => {
                    let region = self.delegate.replace_region(br);
                    if let ReBound(debruijn1, br) = region {
                        // If the callback returns a late-bound region,
                        // that region should always use the INNERMOST
                        // debruijn index. Then we adjust it to the
                        // correct depth.
                        tracked_span_assert_eq!(debruijn1, INNERMOST);
                        Region::ReBound(debruijn, br)
                    } else {
                        region
                    }
                }
                Ordering::Greater => ReBound(debruijn.shifted_out(1), br),
            }
        } else {
            *re
        }
    }
}

/// Substitution for generics, i.e., early bound types, lifetimes, const generics, and refinements.
/// Note that a substitution for refinement parameters (a list of expressions) must always be
/// specified, while the behavior of other generics parameters (types, lifetimes and consts) can be
/// configured with [`GenericsSubstDelegate`].
pub struct GenericsSubstFolder<'a, D> {
    current_index: DebruijnIndex,
    delegate: D,
    refinement_args: &'a [Expr],
}

pub trait GenericsSubstDelegate {
    type Error = !;

    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, Self::Error>;
    fn ty_for_param(&mut self, param_ty: ParamTy) -> Result<Ty, Self::Error>;
    fn ctor_for_param(&mut self, param_ty: ParamTy) -> Result<SubsetTyCtor, Self::Error>;
    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region;
    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr;
    fn const_for_param(&mut self, param: &Const) -> Const;
}

/// A substitution with an explicit list of generic arguments.
pub(crate) struct GenericArgsDelegate<'a, 'tcx>(
    pub(crate) &'a [GenericArg],
    pub(crate) TyCtxt<'tcx>,
);

impl GenericsSubstDelegate for GenericArgsDelegate<'_, '_> {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, !> {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => Ok(ctor.sort()),
            Some(arg) => {
                tracked_span_bug!("expected base type for generic parameter, found `{arg:?}`")
            }
            None => tracked_span_bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Result<Ty, !> {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Ty(ty)) => Ok(ty.clone()),
            Some(arg) => tracked_span_bug!("expected type for generic parameter, found `{arg:?}`"),
            None => tracked_span_bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> Result<SubsetTyCtor, !> {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => Ok(ctor.clone()),
            Some(arg) => {
                tracked_span_bug!("expected base type for generic parameter, found `{arg:?}`")
            }
            None => tracked_span_bug!("type parameter out of range"),
        }
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        match self.0.get(ebr.index as usize) {
            Some(GenericArg::Lifetime(re)) => *re,
            Some(arg) => bug!("expected region for generic parameter, found `{arg:?}`"),
            None => bug!("region parameter out of range"),
        }
    }

    fn const_for_param(&mut self, param: &Const) -> Const {
        if let ConstKind::Param(param_const) = &param.kind {
            match self.0.get(param_const.index as usize) {
                Some(GenericArg::Const(cst)) => cst.clone(),
                Some(arg) => bug!("expected const for generic parameter, found `{arg:?}`"),
                None => bug!("generic parameter out of range"),
            }
        } else {
            param.clone()
        }
    }

    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr {
        match self.0.get(param_const.index as usize) {
            Some(GenericArg::Const(cst)) => Expr::from_const(self.1, cst),
            Some(arg) => bug!("expected const for generic parameter, found `{arg:?}`"),
            None => bug!("generic parameter out of range"),
        }
    }
}

/// A substitution meant to be used only for sorts. It'll panic if used on a type. This is used to
/// break cycles during wf checking. During wf-checking we use [`rty::Sort`], but we can't yet
/// generate (in general) an [`rty::GenericArg`] because conversion from [`fhir`] into [`rty`]
/// requires the results of wf checking. Perhaps, we could also solve this problem by doing
/// wf-checking with a different "IR" for sorts that sits in between [`fhir`] and [`rty`].
///
/// [`rty::Sort`]: crate::rty::Sort
/// [`rty::GenericArg`]: crate::rty::GenericArg
/// [`fhir`]: crate::fhir
/// [`rty`]: crate::rty
pub(crate) struct GenericsSubstForSort<F, E>
where
    F: FnMut(ParamTy) -> Result<Sort, E>,
{
    /// Implementation of [`GenericsSubstDelegate::sort_for_param`]
    pub(crate) sort_for_param: F,
}

impl<F, E> GenericsSubstDelegate for GenericsSubstForSort<F, E>
where
    F: FnMut(ParamTy) -> Result<Sort, E>,
{
    type Error = E;

    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, E> {
        (self.sort_for_param)(param_ty)
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Result<Ty, E> {
        bug!("unexpected type param {param_ty:?}");
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> Result<SubsetTyCtor, E> {
        bug!("unexpected base type param {param_ty:?}");
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        bug!("unexpected region param {ebr:?}");
    }

    fn const_for_param(&mut self, param: &Const) -> Const {
        bug!("unexpected const param {param:?}");
    }

    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr {
        bug!("unexpected param_const {param_const:?}");
    }
}

impl<'a, D> GenericsSubstFolder<'a, D> {
    pub fn new(delegate: D, refine: &'a [Expr]) -> Self {
        Self { current_index: INNERMOST, delegate, refinement_args: refine }
    }
}

impl<D: GenericsSubstDelegate> FallibleTypeFolder for GenericsSubstFolder<'_, D> {
    type Error = D::Error;

    fn try_enter_binder(&mut self, _: &BoundVariableKinds) {
        self.current_index.shift_in(1);
    }

    fn try_exit_binder(&mut self) {
        self.current_index.shift_out(1);
    }

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, D::Error> {
        if let Sort::Param(param_ty) = sort {
            self.delegate.sort_for_param(*param_ty)
        } else {
            sort.try_super_fold_with(self)
        }
    }

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, D::Error> {
        match ty.kind() {
            TyKind::Param(param_ty) => self.delegate.ty_for_param(*param_ty),
            TyKind::Indexed(BaseTy::Param(param_ty), idx) => {
                let idx = idx.try_fold_with(self)?;
                Ok(self
                    .delegate
                    .ctor_for_param(*param_ty)?
                    .replace_bound_reft(&idx)
                    .to_ty())
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_subset_ty(&mut self, sty: &SubsetTy) -> Result<SubsetTy, D::Error> {
        if let BaseTy::Param(param_ty) = &sty.bty {
            let idx = sty.idx.try_fold_with(self)?;
            let pred = sty.pred.try_fold_with(self)?;
            Ok(self
                .delegate
                .ctor_for_param(*param_ty)?
                .replace_bound_reft(&idx)
                .strengthen(pred))
        } else {
            sty.try_super_fold_with(self)
        }
    }

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, D::Error> {
        if let ReEarlyParam(ebr) = *re { Ok(self.delegate.region_for_param(ebr)) } else { Ok(*re) }
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, D::Error> {
        match expr.kind() {
            ExprKind::Var(Var::EarlyParam(var)) => Ok(self.expr_for_param(var.index)),
            ExprKind::Var(Var::ConstGeneric(param_const)) => {
                Ok(self.delegate.expr_for_param_const(*param_const))
            }
            _ => expr.try_super_fold_with(self),
        }
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, D::Error> {
        Ok(self.delegate.const_for_param(c))
    }
}

impl<D> GenericsSubstFolder<'_, D> {
    fn expr_for_param(&self, idx: u32) -> Expr {
        self.refinement_args[idx as usize].shift_in_escaping(self.current_index.as_u32())
    }
}

pub(crate) struct SortSubst<D> {
    delegate: D,
}

impl<D> SortSubst<D> {
    pub(crate) fn new(delegate: D) -> Self {
        Self { delegate }
    }
}

impl<D: SortSubstDelegate> TypeFolder for SortSubst<D> {
    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        match sort {
            Sort::Var(var) => self.delegate.sort_for_param(*var),
            Sort::BitVec(BvSize::Param(var)) => Sort::BitVec(self.delegate.bv_size_for_param(*var)),
            _ => sort.super_fold_with(self),
        }
    }
}

trait SortSubstDelegate {
    fn sort_for_param(&self, var: ParamSort) -> Sort;
    fn bv_size_for_param(&self, var: ParamSort) -> BvSize;
}

impl SortSubstDelegate for &[SortArg] {
    fn sort_for_param(&self, var: ParamSort) -> Sort {
        match &self[var.index()] {
            SortArg::Sort(sort) => sort.clone(),
            SortArg::BvSize(_) => tracked_span_bug!("unexpected bv size for sort param"),
        }
    }

    fn bv_size_for_param(&self, var: ParamSort) -> BvSize {
        match self[var.index()] {
            SortArg::BvSize(size) => size,
            SortArg::Sort(_) => tracked_span_bug!("unexpected sort for bv size param"),
        }
    }
}

impl SortSubstDelegate for &[Sort] {
    fn sort_for_param(&self, var: ParamSort) -> Sort {
        self[var.index()].clone()
    }

    fn bv_size_for_param(&self, _var: ParamSort) -> BvSize {
        tracked_span_bug!("unexpected bv size parameter")
    }
}
