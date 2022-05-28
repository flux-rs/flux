use rustc_hash::FxHashMap;

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
