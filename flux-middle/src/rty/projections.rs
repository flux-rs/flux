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
    ty::{Binder, List, TraitPredicate, TraitRef, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    AliasKind, AliasTy, BaseTy, ClauseKind, GenericArg, GenericPredicates, Ty, TyKind,
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

fn into_rustc_generic_arg<'tcx>(
    tcx: &TyCtxt<'tcx>,
    bty: &GenericArg,
) -> rustc_middle::ty::GenericArg<'tcx> {
    match bty {
        GenericArg::Ty(ty) => rustc_middle::ty::GenericArg::from(into_rustc_ty(tcx, ty)),
        GenericArg::BaseTy(bty) => {
            rustc_middle::ty::GenericArg::from(into_rustc_ty(tcx, &bty.clone().skip_binder()))
        }
        GenericArg::Lifetime(_) => todo!(),
    }
}
fn into_rustc_bty<'tcx>(tcx: &TyCtxt<'tcx>, bty: &BaseTy) -> rustc_middle::ty::Ty<'tcx> {
    match bty {
        BaseTy::Int(i) => tcx.mk_mach_int(*i), // rustc_middle::ty::Ty::mk_int(*tcx, int_ty),
        BaseTy::Uint(i) => tcx.mk_mach_uint(*i),
        BaseTy::Param(pty) => pty.to_ty(*tcx),
        BaseTy::Slice(ty) => tcx.mk_slice(into_rustc_ty(tcx, ty)),
        BaseTy::Bool => todo!(),
        BaseTy::Str => tcx.mk_static_str(),
        BaseTy::Char => todo!(),
        BaseTy::Adt(adt_def, substs) => {
            let did = adt_def.did();
            let adt_def = tcx.adt_def(did);
            let substs = substs.iter().map(|arg| into_rustc_generic_arg(tcx, arg));
            let substs = tcx.mk_substs_from_iter(substs);
            tcx.mk_adt(adt_def, substs)
        }
        BaseTy::Float(_) => todo!(),
        BaseTy::RawPtr(_, _) => todo!(),
        BaseTy::Ref(_, _, _) => todo!(),
        BaseTy::Tuple(_) => todo!(),
        BaseTy::Array(_, _) => todo!(),
        BaseTy::Never => todo!(),
        BaseTy::Closure(_, _) => todo!(),
        BaseTy::Alias(_, _) => todo!(),
    }
}

fn into_rustc_ty<'tcx>(tcx: &TyCtxt<'tcx>, ty: &Ty) -> rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Indexed(bty, _) => into_rustc_bty(tcx, bty),
        TyKind::Exists(ty) => into_rustc_ty(tcx, &ty.clone().skip_binder()),
        TyKind::Constr(_, ty) => into_rustc_ty(tcx, ty),
        TyKind::Param(pty) => pty.to_ty(*tcx),
        TyKind::Uninit => todo!(),
        TyKind::Ptr(_, _) => todo!(),
        TyKind::Discr(_, _) => todo!(),
        TyKind::Downcast(_, _, _, _, _) => todo!(),
        TyKind::Blocked(_) => todo!(),
    }
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

    let trait_def_id = tcx.parent(elem);

    let predicate = TraitPredicate {
        trait_ref: TraitRef::new(
            *tcx,
            trait_def_id,
            vec![into_rustc_ty(tcx, impl_rty)],
            // elem,
            // vec![into_rustc_ty(tcx, impl_rty), into_rustc_ty(tcx, term)],
        ),
        constness: rustc_middle::ty::BoundConstness::ConstIfConst,
        polarity: rustc_middle::ty::ImplPolarity::Positive,
    };
    let predicate = Binder::dummy(predicate);
    let cause = ObligationCause::dummy(); // TODO(RJ): use with_span instead of `dummy`
    let param_env = tcx.param_env(callsite_def_id);
    let recursion_depth = 5; // TODO(RJ): made up a random number!
    let oblig = Obligation { cause, param_env, predicate, recursion_depth };
    let selection_result = sel_ctxt.select(&oblig);
    println!("selection_result: {predicate:?} with {selection_result:?}");
    // 3. subst-hacks to recover the rty::Ty

    todo!("resolve_impl_projection: {impl_rty:?} {elem:?}");
}
