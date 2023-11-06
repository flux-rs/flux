use std::{cmp::Ordering, collections::hash_map, slice};

use flux_common::bug;
use rustc_data_structures::unord::UnordMap;
use rustc_middle::ty::RegionVid;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{
    evars::EVarSol,
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
};
use crate::{rty::*, rustc};

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
                if let ReVar(rvid) = re && let Some(region) = self.0.map.get(rvid) {
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
            (BaseTy::Adt(_adt1, args1), ty::TyKind::Adt(_adt2, args2)) => {
                // println!(
                //     "TRACE: infer_from_bty: ( {:?}, args1 = {args1:?}) ({:?}, args2 = {args2:?}",
                //     adt1.did(),
                //     adt2.did()
                // );
                debug_assert_eq!(args1.len(), args2.len());
                for (arg1, arg2) in iter::zip(args1, args2) {
                    match (arg1, arg2) {
                        (GenericArg::BaseTy(ty_con), ty::GenericArg::Ty(ty2)) => {
                            self.infer_from_ty(ty_con.as_ref().skip_binder(), ty2);
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
    fn replace_expr(&mut self, idx: u32) -> Expr;
    fn replace_region(&mut self, br: BoundRegion) -> Region;
}

pub(crate) struct FnMutDelegate<F1, F2> {
    pub exprs: F1,
    pub regions: F2,
}

impl<F1, F2> BoundVarReplacerDelegate for FnMutDelegate<F1, F2>
where
    F1: FnMut(u32) -> Expr,
    F2: FnMut(BoundRegion) -> Region,
{
    fn replace_expr(&mut self, idx: u32) -> Expr {
        (self.exprs)(idx)
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
        if let ExprKind::Var(Var::LateBound(debruijn, idx)) = e.kind() {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => Expr::late_bvar(*debruijn, *idx),
                Ordering::Equal => {
                    self.delegate
                        .replace_expr(*idx)
                        .shift_in_escaping(self.current_index.as_u32())
                }
                Ordering::Greater => Expr::late_bvar(debruijn.shifted_out(1), *idx),
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
        if let ExprKind::Var(Var::EVar(evar)) = e.kind() && let Some(sol) = self.evars.get(*evar) {
            sol.clone()
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for generics, i.e., early bound types, lifetimes, const generics and refinements
pub(super) struct GenericsSubstFolder<'a> {
    current_index: DebruijnIndex,
    /// We leave this as [None] if we only want to substitute the EarlyBound refinement-params
    generics: Option<&'a [GenericArg]>,
    refine: &'a [Expr],
}

impl<'a> GenericsSubstFolder<'a> {
    pub(super) fn new(generics: Option<&'a [GenericArg]>, refine: &'a [Expr]) -> Self {
        Self { current_index: INNERMOST, generics, refine }
    }
}

impl TypeFolder for GenericsSubstFolder<'_> {
    fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
        self.current_index.shift_in(1);
        let r = t.super_fold_with(self);
        self.current_index.shift_out(1);
        r
    }

    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        if let Sort::Param(param_ty) = sort {
            self.sort_for_param(*param_ty)
        } else {
            sort.super_fold_with(self)
        }
    }

    // [NOTE:index-subst]

    // Consider

    // ```rust
    // fn choose <T as base>(b: bool, x: T[@n], y: T[@m]) -> T[if b { n } else { m }])
    // ```

    // and then a client

    // ```rust
    // pub fn test01() {
    //     assert(choose(true, 0, 1) == 0);
    // }
    // ```

    // At the callsite `choose(true, 0, 1)` there are *two* substitutions going on
    // in the signature for `choose` i.e. for the `T[@n]` and `T[@m]`

    // 1. `T` -> `i32{v: ...}`
    // 2. earlybound `n, m` -> fresh-evars.

    // The trouble is that if you solely rely on the `bty_for_param` code below,
    // then the `n, m` substitutions "get lost" and so those variables are not
    // "solved for" and you get that pesky instantiation error.

    // Instead, we _first_ substitute for the indices, and then let `bty_for_param`
    // do its business.

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Param(param_ty) => self.ty_for_param(*param_ty),
            TyKind::Indexed(BaseTy::Param(param_ty), idx) => {
                // See [NOTE:index-subst]
                let idx = idx.fold_with(self);
                self.bty_for_param(*param_ty, &idx)
            }
            _ => ty.super_fold_with(self),
        }
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        if let ReEarlyBound(ebr) = *re {
            self.region_for_param(ebr)
        } else {
            *re
        }
    }

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        if let ExprKind::Var(Var::EarlyBound(idx)) = expr.kind() {
            self.expr_for_param(*idx)
        } else {
            expr.super_fold_with(self)
        }
    }
}

impl GenericsSubstFolder<'_> {
    fn sort_for_param(&self, param_ty: ParamTy) -> Sort {
        if let Some(generics) = self.generics {
            match generics.get(param_ty.index as usize) {
                Some(GenericArg::BaseTy(arg)) => {
                    if let [BoundVariableKind::Refine(sort, _)] = &arg.vars()[..] {
                        sort.clone()
                    } else {
                        bug!("unexpected bound variable `{arg:?}`")
                    }
                }
                Some(arg) => bug!("expected base type for generic parameter, found `{arg:?}`"),
                None => bug!("type parameter out of range {param_ty:?}"),
            }
        } else {
            Sort::Param(param_ty)
        }
    }

    fn ty_for_param(&self, param_ty: ParamTy) -> Ty {
        if let Some(generics) = self.generics {
            match generics.get(param_ty.index as usize) {
                Some(GenericArg::Ty(ty)) => ty.clone(),
                Some(arg) => bug!("expected type for generic parameter, found `{:?}`", arg),
                None => bug!("type parameter out of range"),
            }
        } else {
            Ty::param(param_ty)
        }
    }

    fn bty_for_param(&self, param_ty: ParamTy, idx: &Index) -> Ty {
        if let Some(generics) = self.generics {
            match generics.get(param_ty.index as usize) {
                Some(GenericArg::BaseTy(arg)) => {
                    arg.replace_bound_exprs(slice::from_ref(&idx.expr))
                }
                Some(arg) => bug!("expected base type for generic parameter, found `{:?}`", arg),
                None => bug!("type parameter out of range"),
            }
        } else {
            Ty::indexed(BaseTy::Param(param_ty), idx.clone())
        }
    }

    fn region_for_param(&self, ebr: EarlyBoundRegion) -> Region {
        if let Some(generics) = self.generics {
            match generics.get(ebr.index as usize) {
                Some(GenericArg::Lifetime(re)) => *re,
                Some(arg) => bug!("expected region for generic parameter, found `{:?}`", arg),
                None => bug!("region parameter out of range"),
            }
        } else {
            ReEarlyBound(ebr)
        }
    }

    fn expr_for_param(&self, idx: u32) -> Expr {
        self.refine[idx as usize].shift_in_escaping(self.current_index.as_u32())
    }
}
