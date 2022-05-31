use rustc_hash::{FxHashMap, FxHashSet};

use crate::ty::*;

use super::fold::{TypeFoldable, TypeFolder};

#[derive(Debug)]
pub struct Subst<'a> {
    fvar_map: FxHashMap<Name, Expr>,
    generics: &'a [Ty],
}

impl Subst<'_> {
    pub fn empty() -> Self {
        Subst { generics: &[], fvar_map: FxHashMap::default() }
    }

    pub fn with_type_substs(types: &[Ty]) -> Subst {
        Subst { generics: types, fvar_map: FxHashMap::default() }
    }

    pub fn insert(&mut self, from: Name, to: impl Into<Expr>) -> Option<Expr> {
        self.fvar_map.insert(from, to.into())
    }

    pub fn contains(&self, from: Name) -> bool {
        self.fvar_map.contains_key(&from)
    }

    pub fn apply<T: TypeFoldable>(&self, t: &T) -> T {
        t.fold_with(&mut SubstFolder { subst: self })
    }

    pub fn subst_loc(&self, loc: Loc) -> Loc {
        let loc_expr = self.apply(&loc.to_expr());
        loc_expr
            .to_loc()
            .unwrap_or_else(|| panic!("substitution produces invalid loc: {loc_expr:?}"))
    }

    pub fn infer_from_exprs(&mut self, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
        match (e1.kind(), e2.kind()) {
            (_, ExprKind::FreeVar(fvar)) if params.contains(fvar) => {
                if let Some(old_e) = self.insert(*fvar, e1.clone()) {
                    if &old_e != e2 {
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

struct SubstFolder<'a, 'b> {
    subst: &'a Subst<'b>,
}

impl TypeFolder for SubstFolder<'_, '_> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        if let TyKind::Param(param_ty) = ty.kind() {
            self.subst
                .generics
                .get(param_ty.index as usize)
                .cloned()
                .unwrap_or_else(|| ty.clone())
        } else {
            ty.super_fold_with(self)
        }
    }

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
