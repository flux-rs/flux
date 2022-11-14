use rustc_hash::{FxHashMap, FxHashSet};

use super::fold::{TypeFoldable, TypeFolder};
use crate::rty::*;

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
        t.fold_with(&mut FVarFolder { subst: self })
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        let loc_expr = self.apply(&loc.to_expr());
        loc_expr
            .to_loc()
            .unwrap_or_else(|| panic!("substitution produces invalid loc: {loc_expr:?}"))
    }
    pub fn infer_from_refine_args(
        &mut self,
        params: &FxHashSet<Name>,
        arg1: &RefineArg,
        arg2: &RefineArg,
    ) {
        if let (RefineArg::Expr(e1), RefineArg::Expr(e2)) = (arg1, arg2) {
            self.infer_from_exprs(params, e1, e2);
        }
    }

    pub fn infer_from_exprs(&mut self, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::FreeVar(fvar)) if params.contains(fvar) => {
                if let Some(old_e) = self.insert(*fvar, e1.clone()) {
                    if &old_e != e1 {
                        todo!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *fvar,
                            old_e,
                            e1
                        )
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

struct FVarFolder<'a> {
    subst: &'a FVarSubst,
}

impl TypeFolder for FVarFolder<'_> {
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

pub(super) struct BVarFolder<'a> {
    outer_binder: DebruijnIndex,
    args: &'a [RefineArg],
}

impl<'a> BVarFolder<'a> {
    pub(super) fn new(args: &'a [RefineArg]) -> BVarFolder<'a> {
        BVarFolder { args, outer_binder: INNERMOST }
    }
}

impl TypeFolder for BVarFolder<'_> {
    fn fold_binders<T>(&mut self, t: &Binders<T>) -> Binders<T>
    where
        T: TypeFoldable,
    {
        self.outer_binder.shift_in(1);
        let r = t.super_fold_with(self);
        self.outer_binder.shift_out(1);
        r
    }

    fn fold_refine_arg(&mut self, arg: &RefineArg) -> RefineArg {
        if let RefineArg::Expr(expr) = arg
           && let ExprKind::BoundVar(bvar) = expr.kind()
           && bvar.debruijn == self.outer_binder
        {
            self.args[bvar.index].clone()
        } else {
            arg.super_fold_with(self)
        }
    }

    fn fold_pred(&mut self, pred: &Pred) -> Pred {
        if let Pred::App(Var::Bound(bvar), args) = pred
           && bvar.debruijn == self.outer_binder
           && let RefineArg::Abs(pred_abs) = &self.args[bvar.index]
        {
            let args = args.iter().map(|arg| RefineArg::Expr(arg.fold_with(self))).collect_vec();
            pred_abs.replace_bound_vars(&args)
        } else {
            pred.super_fold_with(self)
        }
    }

    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::BoundVar(bvar) = e.kind() && bvar.debruijn == self.outer_binder {
            if let RefineArg::Expr(e) = &self.args[bvar.index] {
                e.clone()
            } else {
                panic!("expected expr for `{bvar:?}` but found `{:?}` when substituting", self.args[bvar.index])
            }
        } else {
            e.super_fold_with(self)
        }
    }
}
