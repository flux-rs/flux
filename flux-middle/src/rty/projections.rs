use flux_common::bug;
use rustc_hash::FxHashMap;

use super::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    AliasKind, AliasTy, BaseTy, ClauseKind, GenericPredicates, Ty, TyKind,
};

#[derive(Debug)]
struct ProjectionTable(FxHashMap<AliasTy, Ty>);

impl ProjectionTable {
    pub fn new(predicates: GenericPredicates) -> Self {
        let mut res = FxHashMap::default();
        for pred in &predicates.predicates {
            if pred.kind.vars().is_empty() {
                if let ClauseKind::Projection(proj_pred) = pred.kind.clone().skip_binder() {
                    match res.insert(proj_pred.projection_ty, proj_pred.term) {
                        None => (),
                        Some(_) => bug!("duplicate projection predicate"),
                    }
                }
            }
        }
        ProjectionTable(res)
    }

    pub fn resolve(&self, alias_ty: &AliasTy) -> Ty {
        let alias_ty = without_constrs(alias_ty);
        match self.0.get(&alias_ty) {
            Some(ty) => ty.clone(),
            None => panic!("cannot resolve {alias_ty:?} in {self:?}"),
        }
    }
}
struct WithoutConstrs;

impl TypeFolder for WithoutConstrs {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Constr(_, ty) => ty.fold_with(self),
            _ => ty.super_fold_with(self),
        }
    }
}
/// Turns each Constr(e, T) into T
fn without_constrs<T: TypeFoldable>(t: &T) -> T {
    t.fold_with(&mut WithoutConstrs)
}

struct WithPredicates {
    proj_table: ProjectionTable,
}

impl TypeFolder for WithPredicates {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Alias(AliasKind::Projection, alias_ty), _idx) => {
                // TODO(RJ): ignoring the idx -- but shouldn't `Projection` be a TyKind and not in BaseTy?
                self.proj_table.resolve(alias_ty)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

pub fn normalize_projections<T: TypeFoldable>(t: &T, predicates: GenericPredicates) -> T {
    t.fold_with(&mut WithPredicates { proj_table: ProjectionTable::new(predicates) })
}
