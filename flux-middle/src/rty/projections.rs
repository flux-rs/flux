#[allow(unused_imports)]
use flux_common::bug;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::{
    infer::{InferCtxtBuilder, TyCtxtInferExt},
    traits::Obligation,
};
use rustc_middle::{
    traits::{DefiningAnchor, ObligationCause},
    ty::{Binder, TraitPredicate, TraitRef, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

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

fn into_rustc_ty<'tcx>(_tcx: &TyCtxt<'tcx>, ty: &Ty) -> rustc_middle::ty::Ty<'tcx> {
    todo!("into_rustc_ty")
}

pub fn resolve_impl_projection(
    tcx: &TyCtxt,
    callsite_def_id: DefId,
    impl_rty: &Ty,
    elem: DefId,
    term: &Ty,
) -> Ty {
    // 1. rty -> ty
    // 2. lookup impl selection/trait blah
    let inf_ctxt = tcx.infer_ctxt().build();
    let mut sel_ctxt = SelectionContext::new(&inf_ctxt);

    let predicate = TraitPredicate {
        trait_ref: TraitRef::new(
            *tcx,
            elem,
            vec![into_rustc_ty(tcx, impl_rty), into_rustc_ty(tcx, term)],
        ),
        constness: rustc_middle::ty::BoundConstness::ConstIfConst,
        polarity: rustc_middle::ty::ImplPolarity::Negative,
    };
    let predicate = Binder::dummy(predicate);
    let cause = ObligationCause::dummy(); // TODO(RJ): use with_span instead of `dummy`
    let param_env = tcx.param_env(callsite_def_id);
    let recursion_depth = 5; // TODO(RJ): made up a random number!
    let oblig = Obligation { cause, param_env, predicate, recursion_depth };
    let selection_result = sel_ctxt.select(&oblig);
    println!("selection_result: {elem:?} with {selection_result:?}");
    // 3. subst-hacks to recover the rty::Ty

    todo!("resolve_impl_projection: {impl_rty:?} {elem:?}");
}
