use std::{cmp::Ordering, collections::hash_map};

use flux_common::bug;
use rustc_middle::ty::RegionVid;
use rustc_type_ir::DebruijnIndex;

use super::{
    evars::EVarSol,
    fold::{TypeFolder, TypeSuperFoldable},
};
use crate::rty::*;

#[derive(Debug)]
pub struct RegionSubst {
    map: UnordMap<RegionVid, Region>,
}

impl RegionSubst {
    pub fn new(ty1: &Ty, ty2: &rustc::ty::Ty) -> Self {
        let mut subst = RegionSubst { map: UnordMap::default() };
        subst.infer_from_ty(ty1, ty2);
        subst
    }

    pub fn apply<T: TypeFoldable>(&self, t: &T) -> T {
        struct Folder<'a>(&'a RegionSubst);
        impl TypeFolder for Folder<'_> {
            fn fold_region(&mut self, re: &Region) -> Region {
                if let ReVar(rvid) = re
                    && let Some(region) = self.0.map.get(rvid)
                {
                    *region
                } else {
                    *re
                }
            }
        }
        t.fold_with(&mut Folder(self))
    }

    fn infer_from_ty(&mut self, ty1: &Ty, ty2: &rustc::ty::Ty) {
        use rustc::ty;
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(ty1), _) => {
                self.infer_from_ty(ty1.as_ref().skip_binder(), ty2);
            }
            (TyKind::Constr(_, ty1), _) => {
                self.infer_from_ty(ty1, ty2);
            }
            (TyKind::Indexed(bty, _), _) => {
                self.infer_from_bty(bty, ty2);
            }
            (TyKind::Ptr(PtrKind::Shr(r1), _), ty::TyKind::Ref(r2, _, Mutability::Not))
            | (TyKind::Ptr(PtrKind::Mut(r1), _), ty::TyKind::Ref(r2, _, Mutability::Mut)) => {
                self.infer_from_region(*r1, *r2);
            }
            _ => {}
        }
    }

    fn infer_from_bty(&mut self, bty: &BaseTy, ty: &rustc::ty::Ty) {
        use rustc::ty;
        match (bty, ty.kind()) {
            (BaseTy::Ref(r1, ty1, _), ty::TyKind::Ref(r2, ty2, _)) => {
                self.infer_from_region(*r1, *r2);
                self.infer_from_ty(ty1, ty2);
            }
            (BaseTy::Adt(_, args1), ty::TyKind::Adt(_, args2)) => {
                debug_assert_eq!(args1.len(), args2.len());
                for (arg1, arg2) in iter::zip(args1, args2) {
                    match (arg1, arg2) {
                        (GenericArg::Base(ctor1), ty::GenericArg::Ty(ty2)) => {
                            self.infer_from_bty(ctor1.as_bty_skipping_binder(), ty2);
                        }
                        (GenericArg::Ty(ty1), ty::GenericArg::Ty(ty2)) => {
                            self.infer_from_ty(ty1, ty2);
                        }
                        (GenericArg::Lifetime(re1), ty::GenericArg::Lifetime(re2)) => {
                            self.infer_from_region(*re1, *re2);
                        }
                        _ => {}
                    }
                }
            }
            (BaseTy::Tuple(fields1), ty::TyKind::Tuple(fields2)) => {
                debug_assert_eq!(fields1.len(), fields2.len());
                for (ty1, ty2) in iter::zip(fields1, fields2) {
                    self.infer_from_ty(ty1, ty2);
                }
            }
            _ => {}
        }
    }

    fn infer_from_region(&mut self, re1: Region, re2: Region) {
        let ReVar(var) = re1 else { return };
        match self.map.entry(var) {
            hash_map::Entry::Occupied(entry) => {
                if entry.get() != &re2 {
                    bug!(
                        "ambiguous region substitution: {:?} -> [{:?}, {:?}]",
                        re1,
                        entry.get(),
                        re2
                    );
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(re2);
            }
        }
    }
}

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
    fn fold_binder<T>(&mut self, t: &Binder<T>) -> Binder<T>
    where
        T: TypeFoldable,
    {
        self.current_index.shift_in(1);
        let r = t.super_fold_with(self);
        self.current_index.shift_out(1);
        r
    }

    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::Var(Var::LateBound(debruijn, var)) = e.kind() {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => Expr::late_bvar(*debruijn, var.index, var.kind),
                Ordering::Equal => {
                    self.delegate
                        .replace_expr(*var)
                        .shift_in_escaping(self.current_index.as_u32())
                }
                Ordering::Greater => Expr::late_bvar(debruijn.shifted_out(1), var.index, var.kind),
            }
        } else {
            e.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        if let ReLateBound(debruijn, br) = *re {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => *re,
                Ordering::Equal => {
                    let region = self.delegate.replace_region(br);
                    if let ReLateBound(debruijn1, br) = region {
                        // If the callback returns a late-bound region,
                        // that region should always use the INNERMOST
                        // debruijn index. Then we adjust it to the
                        // correct depth.
                        assert_eq!(debruijn1, INNERMOST);
                        Region::ReLateBound(debruijn, br)
                    } else {
                        region
                    }
                }
                Ordering::Greater => ReLateBound(debruijn.shifted_out(1), br),
            }
        } else {
            *re
        }
    }
}

/// Substitution for [existential variables]
///
/// [existential variables]: crate::rty::Var::EVar
pub(super) struct EVarSubstFolder<'a> {
    evars: &'a EVarSol,
}

impl<'a> EVarSubstFolder<'a> {
    pub(super) fn new(evars: &'a EVarSol) -> Self {
        Self { evars }
    }
}

impl TypeFolder for EVarSubstFolder<'_> {
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::Var(Var::EVar(evar)) = e.kind()
            && let Some(sol) = self.evars.get(*evar)
        {
            sol.clone()
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for generics, i.e., early bound types, lifetimes, const generics, and refinements.
/// Note that a substitution for refinement parameters (a list of expressions) must always be
/// specified, while the behavior of other generics parameters (types, lifetimes and consts) can be
/// configured with [`GenericsSubstDelegate`].
pub(crate) struct GenericsSubstFolder<'a, D> {
    current_index: DebruijnIndex,
    delegate: D,
    refinement_args: &'a [Expr],
}

trait GenericsSubstDelegate {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Sort;
    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty;
    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor;
    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region;
}

/// The identity substitution used when checking the body of a (polymorphic) function. For example,
/// consider the function `fn foo<T>(){ .. }`
///
/// Outside of `foo`, `T` is bound (represented by the presence of `EarlyBinder`). Inside of the body
/// of `foo`, we treat `T` as a placeholder.
pub(crate) struct IdentitySubstDelegate;

impl GenericsSubstDelegate for IdentitySubstDelegate {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Sort {
        Sort::Param(param_ty)
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        Ty::param(param_ty)
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        Binder::with_sort(
            SubsetTy::trivial(BaseTy::Param(param_ty), Expr::nu()),
            Sort::Param(param_ty),
        )
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        ReEarlyBound(ebr)
    }
}

/// A substitution with an explicit list of generic arguments.
pub(crate) struct GenericArgsDelegate<'a>(pub(crate) &'a [GenericArg]);

impl GenericsSubstDelegate for GenericArgsDelegate<'_> {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Sort {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => ctor.sort(),
            Some(arg) => bug!("extected base type for generic parameter, found `{arg:?}`"),
            None => bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Ty(ty)) => ty.clone(),
            Some(arg) => bug!("expected type for generic parameter, found `{arg:?}`"),
            None => bug!("type parameter out of range"),
        }
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => ctor.clone(),
            Some(arg) => bug!("expected base type for generic parameter, found `{arg:?}`"),
            None => bug!("type parameter out of range"),
        }
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        match self.0.get(ebr.index as usize) {
            Some(GenericArg::Lifetime(re)) => *re,
            Some(arg) => bug!("expected region for generic parameter, found `{arg:?}`"),
            None => bug!("region parameter out of range"),
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
pub(crate) struct GenericsSubstForSort<F>
where
    F: FnMut(ParamTy) -> Sort,
{
    /// Implementation of [`GenericsSubstDelegate::sort_for_param`]
    pub(crate) sort_for_param: F,
}

impl<F> GenericsSubstDelegate for GenericsSubstForSort<F>
where
    F: FnMut(ParamTy) -> Sort,
{
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Sort {
        (self.sort_for_param)(param_ty)
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        bug!("unexpected type param {param_ty:?}");
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        bug!("unexpected base type param {param_ty:?}");
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        bug!("unexpected region param {ebr:?}");
    }
}

impl<'a, D> GenericsSubstFolder<'a, D> {
    pub(crate) fn new(delegate: D, refine: &'a [Expr]) -> Self {
        Self { current_index: INNERMOST, delegate, refinement_args: refine }
    }
}

impl<D: GenericsSubstDelegate> TypeFolder for GenericsSubstFolder<'_, D> {
    fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
        self.current_index.shift_in(1);
        let r = t.super_fold_with(self);
        self.current_index.shift_out(1);
        r
    }

    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        if let Sort::Param(param_ty) = sort {
            self.delegate.sort_for_param(*param_ty)
        } else {
            sort.super_fold_with(self)
        }
    }

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Param(param_ty) => self.delegate.ty_for_param(*param_ty),
            TyKind::Indexed(BaseTy::Param(param_ty), idx) => {
                let idx = idx.fold_with(self);
                self.delegate
                    .ctor_for_param(*param_ty)
                    .replace_bound_reft(&idx)
                    .to_ty()
            }
            _ => ty.super_fold_with(self),
        }
    }

    fn fold_subset_ty(&mut self, constr: &SubsetTy) -> SubsetTy {
        if let BaseTy::Param(param_ty) = &constr.bty {
            self.delegate
                .ctor_for_param(*param_ty)
                .replace_bound_reft(&constr.idx)
                .strengthen(&constr.pred)
        } else {
            constr.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        if let ReEarlyBound(ebr) = *re {
            self.delegate.region_for_param(ebr)
        } else {
            *re
        }
    }

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        if let ExprKind::Var(Var::EarlyParam(var)) = expr.kind() {
            self.expr_for_param(var.index)
        } else {
            expr.super_fold_with(self)
        }
    }
}

impl<D> GenericsSubstFolder<'_, D> {
    fn expr_for_param(&self, idx: u32) -> Expr {
        self.refinement_args[idx as usize].shift_in_escaping(self.current_index.as_u32())
    }
}

pub(crate) struct SortSubst<'a> {
    args: &'a [Sort],
}

impl<'a> SortSubst<'a> {
    pub(crate) fn new(args: &'a [Sort]) -> Self {
        Self { args }
    }
}

impl TypeFolder for SortSubst<'_> {
    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        if let Sort::Var(var) = sort {
            self.args[var.index].clone()
        } else {
            sort.super_fold_with(self)
        }
    }
}
