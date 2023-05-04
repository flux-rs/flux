use std::{cmp::Ordering, collections::hash_map};

use flux_common::bug;
use rustc_data_structures::unord::UnordMap;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{
    evars::EVarSol,
    fold::{TypeFoldable, TypeFolder},
};
use crate::{rty::*, rustc};

/// A substitution for [free variables]
///
/// [free variables]: `crate::rty::Var::Free`
#[derive(Debug)]
pub struct FVarSubst {
    fvar_map: FxHashMap<Name, Expr>,
}

impl FVarSubst {
    pub fn empty() -> Self {
        FVarSubst { fvar_map: FxHashMap::default() }
    }

    pub fn insert(&mut self, from: Name, to: impl Into<Expr>) -> Option<Expr> {
        self.fvar_map.insert(from, to.into())
    }

    pub fn contains(&self, from: Name) -> bool {
        self.fvar_map.contains_key(&from)
    }

    pub fn apply<T: TypeFoldable>(&self, t: &T) -> T {
        t.fold_with(&mut FVarSubstFolder { subst: self })
            .normalize(&Default::default())
    }

    pub fn infer_from_idxs(&mut self, params: &FxHashSet<Name>, idx1: &Index, idx2: &Index) {
        self.infer_from_exprs(params, &idx1.expr, &idx2.expr);
    }

    fn infer_from_exprs(&mut self, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::Var(Var::Free(name))) if params.contains(name) => {
                if let Some(old_e) = self.insert(*name, e1.clone()) {
                    if &old_e != e1 {
                        bug!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *name,
                            old_e,
                            e1
                        );
                    }
                }
            }
            (ExprKind::Tuple(exprs1), ExprKind::Tuple(exprs2)) => {
                debug_assert_eq!(exprs1.len(), exprs2.len());
                for (e1, e2) in exprs1.iter().zip(exprs2) {
                    self.infer_from_exprs(params, e1, e2);
                }
            }
            (ExprKind::PathProj(e1, field1), ExprKind::PathProj(e2, field2))
                if field1 == field2 =>
            {
                self.infer_from_exprs(params, e1, e2);
            }
            _ => {}
        }
    }
}

struct FVarSubstFolder<'a> {
    subst: &'a FVarSubst,
}

impl TypeFolder for FVarSubstFolder<'_> {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        if let ExprKind::Var(Var::Free(name)) = expr.kind() {
            self.subst
                .fvar_map
                .get(name)
                .cloned()
                .unwrap_or_else(|| expr.clone())
        } else {
            expr.super_fold_with(self)
        }
    }
}

#[derive(Debug)]
pub struct RegionSubst {
    map: UnordMap<Region, Region>,
}

impl RegionSubst {
    pub fn empty() -> Self {
        RegionSubst { map: UnordMap::default() }
    }

    pub fn infer_from_ty(&mut self, ty1: &Ty, ty2: &rustc::ty::Ty) {
        println!("{ty1:?} {ty2:?}");
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
                self.insert(*r1, *r2);
            }
            _ => {}
        }
    }

    fn infer_from_bty(&mut self, bty: &BaseTy, ty: &rustc::ty::Ty) {
        use rustc::ty;
        match (bty, ty.kind()) {
            (BaseTy::Ref(r1, ty1, _), ty::TyKind::Ref(r2, ty2, _)) => {
                self.insert(*r1, *r2);
                self.infer_from_ty(ty1, ty2);
            }
            (BaseTy::Adt(_, substs1), ty::TyKind::Adt(_, substs2)) => {
                debug_assert_eq!(substs1.len(), substs2.len());
                iter::zip(substs1, substs2).for_each(|(arg1, arg2)| {
                    match (arg1, arg2) {
                        (GenericArg::BaseTy(ty_con), ty::GenericArg::Ty(ty2)) => {
                            self.infer_from_ty(ty_con.as_ref().skip_binder(), ty2);
                        }
                        (GenericArg::Ty(ty1), ty::GenericArg::Ty(ty2)) => {
                            self.infer_from_ty(ty1, ty2);
                        }
                        (GenericArg::Lifetime(re1), ty::GenericArg::Lifetime(re2)) => {
                            self.insert(*re1, *re2);
                        }
                        _ => {}
                    }
                });
            }
            _ => {}
        }
    }

    fn insert(&mut self, from: Region, to: Region) {
        match self.map.entry(from) {
            hash_map::Entry::Occupied(entry) => {
                if entry.get() != &to {
                    bug!(
                        "ambiguous region substitution: {:?} -> [{:?}, {:?}]",
                        from,
                        entry.get(),
                        to
                    );
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(to);
            }
        }
    }
}

/// Substitution for [late bound variables]
///
/// [late bound variables]: `crate::rty::Var::LateBound`
pub(super) struct BVarSubstFolder<'a> {
    current_index: DebruijnIndex,
    expr: &'a Expr,
}

impl<'a> BVarSubstFolder<'a> {
    pub(super) fn new(expr: &'a Expr) -> BVarSubstFolder<'a> {
        BVarSubstFolder { expr, current_index: INNERMOST }
    }
}

impl TypeFolder for BVarSubstFolder<'_> {
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
        if let ExprKind::Var(Var::LateBound(debruijn)) = e.kind() {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => Expr::late_bvar(*debruijn),
                Ordering::Equal => self.expr.shift_in_escaping(self.current_index.as_u32()),
                Ordering::Greater => Expr::late_bvar(debruijn.shifted_out(1)),
            }
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for [existential variables]
///
/// [existential variables]: `crate::rty::Var::EVar`
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
    generics: &'a [GenericArg],
    refine: &'a [Expr],
}

impl<'a> GenericsSubstFolder<'a> {
    pub(super) fn new(generics: &'a [GenericArg], refine: &'a [Expr]) -> Self {
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

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Param(param_ty) => self.ty_for_param(*param_ty),
            TyKind::Indexed(BaseTy::Param(param_ty), idx) => self.bty_for_param(*param_ty, idx),
            _ => ty.super_fold_with(self),
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
        match self.generics.get(param_ty.index as usize) {
            Some(GenericArg::BaseTy(arg)) => arg.sort().clone(),
            Some(GenericArg::Ty(arg)) => {
                bug!("expected base type for generic parameter, found `{:?}`", arg)
            }
            Some(GenericArg::Lifetime(_)) => bug!("substitution for lifetimes is not supported"),
            None => bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ty_for_param(&self, param_ty: ParamTy) -> Ty {
        match self.generics.get(param_ty.index as usize) {
            Some(GenericArg::Ty(ty)) => ty.clone(),
            Some(arg) => bug!("expected type for generic parameter, found `{:?}`", arg),
            None => bug!("type parameter out of range"),
        }
    }

    fn bty_for_param(&self, param_ty: ParamTy, idx: &Index) -> Ty {
        match self.generics.get(param_ty.index as usize) {
            Some(GenericArg::BaseTy(arg)) => arg.replace_bvar(&idx.expr),
            Some(arg) => bug!("expected base type for generic parameter, found `{:?}`", arg),
            None => bug!("type parameter out of range"),
        }
    }

    fn expr_for_param(&self, idx: u32) -> Expr {
        self.refine[idx as usize].shift_in_escaping(self.current_index.as_u32())
    }
}
