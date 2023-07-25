use std::iter;

#[allow(unused_imports)]
use flux_common::bug;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::TyCtxtInferExt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSourceUserDefinedData, ObligationCause},
    ty::{Binder, ParamTy, TraitPredicate, TraitRef, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    AliasKind, AliasTy, BaseTy, ClauseKind, GenericArg, GenericPredicates, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    rty::EarlyBinder,
    rustc::{self},
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

#[derive(Debug)]
pub struct TVarSubst {
    map: FxHashMap<ParamTy, Ty>,
}

impl TVarSubst {
    pub fn mk_subst(src: &rustc_middle::ty::Ty, dst: &Ty) -> Vec<GenericArg> {
        let mut subst = TVarSubst { map: FxHashMap::default() };
        subst.infer_from_ty(src, dst);
        subst
            .map
            .iter()
            .sorted_by_key(|(pty, _)| pty.index)
            .map(|(_, ty)| GenericArg::Ty(ty.clone()))
            .collect()
    }

    fn insert(&mut self, pty: &ParamTy, ty: &Ty) {
        match self.map.insert(*pty, ty.clone()) {
            None => (),
            Some(_) => bug!("duplicate insert"),
        }
    }

    fn base_ty(ty: &Ty) -> BaseTy {
        match ty.kind() {
            TyKind::Indexed(bty, _) => bty.clone(),
            TyKind::Exists(b) => Self::base_ty(&b.clone().skip_binder()), // TODO: seems dicey...
            TyKind::Constr(_, ty) => Self::base_ty(ty),
            TyKind::Uninit
            | TyKind::Ptr(_, _)
            | TyKind::Discr(_, _)
            | TyKind::Param(_)
            | TyKind::Downcast(_, _, _, _, _)
            | TyKind::Blocked(_) => bug!("unexpected base_ty"),
        }
    }

    fn infer_from_arg(&mut self, src: &rustc_middle::ty::GenericArg, dst: &GenericArg) {
        if let GenericArg::Ty(dst) = dst {
            self.infer_from_ty(&src.as_type().unwrap(), dst)
        }
    }

    fn infer_from_ty(&mut self, src: &rustc_middle::ty::Ty, dst: &Ty) {
        use rustc_middle::ty;
        match src.kind().clone() {
            ty::TyKind::Param(pty) => self.insert(&pty, dst),
            ty::TyKind::Adt(_, src_subst) => {
                if let BaseTy::Adt(_, dst_subst) = Self::base_ty(dst) {
                    debug_assert_eq!(src_subst.len(), dst_subst.len());
                    iter::zip(src_subst, &dst_subst)
                        .for_each(|(src_arg, dst_arg)| self.infer_from_arg(&src_arg, dst_arg));
                } else {
                    bug!("unexpected base_ty")
                }
            }
            ty::TyKind::Array(src, _) => {
                if let BaseTy::Array(dst, _) = Self::base_ty(dst) {
                    self.infer_from_ty(&src, &dst)
                } else {
                    bug!("unexpected base_ty")
                }
            }

            ty::TyKind::Slice(src) => {
                if let BaseTy::Slice(dst) = Self::base_ty(dst) {
                    self.infer_from_ty(&src, &dst)
                } else {
                    bug!("unexpected base_ty")
                }
            }
            ty::TyKind::Tuple(src_tys) => {
                if let BaseTy::Tuple(dst_tys) = Self::base_ty(dst) {
                    debug_assert_eq!(src_tys.len(), dst_tys.len());
                    iter::zip(src_tys.iter(), dst_tys.iter())
                        .for_each(|(src, dst)| self.infer_from_ty(&src, dst))
                } else {
                    bug!("unexpected base_ty")
                }
            }
            _ => {}
        }
    }
}

fn get_impl_source<'tcx>(
    genv: &GlobalEnv<'_, 'tcx>,
    elem: DefId,
    impl_rty: &Ty,
    callsite_def_id: DefId,
) -> ImplSourceUserDefinedData<'tcx, Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>> {
    // 1a. build up the `Obligation` query
    let trait_def_id = genv.tcx.parent(elem);
    let predicate = Binder::dummy(TraitPredicate {
        trait_ref: TraitRef::new(genv.tcx, trait_def_id, vec![into_rustc_ty(&genv.tcx, impl_rty)]),
        constness: rustc_middle::ty::BoundConstness::NotConst,
        polarity: rustc_middle::ty::ImplPolarity::Positive,
    });
    let oblig = Obligation {
        cause: ObligationCause::dummy(), // TODO(RJ): use with_span instead of `dummy`
        param_env: genv.tcx.param_env(callsite_def_id),
        predicate,
        recursion_depth: 5, // TODO(RJ): made up a random number!
    };

    // 1b. build up the `SelectionContext`
    let inf_ctxt = genv.tcx.infer_ctxt().build();
    let mut sel_ctxt = SelectionContext::new(&inf_ctxt);

    // 1c. issue query to find the `impl` block that implements the `Trait`
    let impl_source = match sel_ctxt.select(&oblig) {
        Ok(Some(rustc_middle::traits::ImplSource::UserDefined(impl_source))) => impl_source,
        Ok(e) => bug!("invalid selection for {oblig:?} = {e:?}"),
        Err(e) => bug!("error selecting {oblig:?}: {e:?}"),
    };
    impl_source
}

/// Given an an `impl_rty` e.g. `std::vec::IntoIter<Nat>` and an `elem` e.g. `std::iter::Iterator::Item`,
/// returns the component of the `impl_rty` that corresponds to the `elem`, e.g. `Nat`.

pub fn resolve_impl_projection(
    genv: &GlobalEnv,
    callsite_def_id: DefId,
    impl_rty: &Ty,
    elem: DefId,
) -> Ty {
    // 1. Use elem == Trait::Item to find the impl-block corresponding to the implementation of `Trait` for the `impl_rty`
    let impl_source = get_impl_source(genv, elem, impl_rty, callsite_def_id);

    // 2. Extract the `DefId` corresponding to `elem` from the impl-block
    // TODO(RJ): is there a faster way to get the def_id of an associated item from an impl?
    let impl_id = genv
        .tcx
        .associated_items(impl_source.impl_def_id)
        .in_definition_order()
        .find(|item| item.trait_item_def_id == Some(elem))
        .map(|item| item.def_id)
        .unwrap();

    // 3. Compute the rty::Ty for `impl_id`
    let impl_ty = genv.tcx.type_of(impl_id).subst_identity();
    let impl_ty = rustc::lowering::lower_ty(genv.tcx, impl_ty).unwrap();
    let impl_ty = genv
        .refine_default(&genv.generics_of(impl_source.impl_def_id).unwrap(), &impl_ty)
        .unwrap();

    // 4. "Unify" the types of the target of the `src` impl trait (e.g. IntoIter<T>) and `dst` impl_rty (e.g. IntoIter<Nat>)
    //     to get a `generics` substitution (e.g. `T` -> `Nat`)
    let src = genv
        .tcx
        .impl_trait_ref(impl_source.impl_def_id)
        .unwrap()
        .skip_binder()
        .substs[0]
        .as_type()
        .unwrap();
    let generics = TVarSubst::mk_subst(&src, impl_rty);

    // 5. Apply the `generics` substitution to the `impl_ty` to get the "resolved" `elem` type
    EarlyBinder(impl_ty).subst(&generics, &[])
}
