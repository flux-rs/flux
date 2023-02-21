use flux_common::bug;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    evars::EVarSol,
    fold::{TypeFoldable, TypeFolder},
};
use crate::rty::*;

/// A substitution for [free variables]
///
/// [free variables]: `crate::rty::ExprKind::FreeVar`
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
            (_, ExprKind::FreeVar(fvar)) if params.contains(fvar) => {
                if let Some(old_e) = self.insert(*fvar, e1.clone()) {
                    if &old_e != e1 {
                        bug!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *fvar,
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
        if let ExprKind::FreeVar(name) = expr.kind() {
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

/// Substitution for [bound variables]
///
/// [bound variables]: `crate::rty::ExprKind::BoundVar`
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
    fn fold_binders<T>(&mut self, t: &Binder<T>) -> Binder<T>
    where
        T: TypeFoldable,
    {
        self.current_index.shift_in(1);
        let r = t.super_fold_with(self);
        self.current_index.shift_out(1);
        r
    }

    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::BoundVar(debruijn) = e.kind() && *debruijn == self.current_index {
            self.expr.shift_in_bvars(self.current_index.as_u32())
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for [existential variables]
///
/// [existential variables]: `crate::rty::ExprKind::EVar`
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
        if let ExprKind::EVar(evar) = e.kind() && let Some(sol) = self.evars.get(*evar) {
            sol.clone()
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for generics (type, lifetimes and const generics). Only substitution for types
/// is implemented. Higher-ranked types are not supported yet, i.e., we only support early bound
/// parameters.
pub(super) struct GenericsSubstFolder<'a> {
    pub(super) substs: &'a [GenericArg],
}

impl TypeFolder for GenericsSubstFolder<'_> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        if let TyKind::Param(param_ty) = ty.kind() {
            self.ty_for_param(*param_ty)
        } else {
            ty.super_fold_with(self)
        }
    }
}

impl GenericsSubstFolder<'_> {
    fn ty_for_param(&self, param_ty: ParamTy) -> Ty {
        match self.substs.get(param_ty.index as usize) {
            Some(GenericArg::Ty(ty)) => ty.clone(),
            Some(GenericArg::Lifetime) => bug!("substitution for lifetimes is not supported"),
            None => bug!("type parameter out of range"),
        }
    }
}
