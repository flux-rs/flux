use std::{iter, ops::ControlFlow};

#[allow(unused_imports)]
use flux_common::bug;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::TyCtxtInferExt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSourceUserDefinedData, ObligationCause},
    ty::{ParamTy, ToPredicate, TraitRef, TyCtxt},
};
use rustc_span::Span;
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitor},
    AliasKind, AliasTy, BaseTy, ClauseKind, GenericArg, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    queries::QueryErr,
    rty::{fold::TypeVisitable, EarlyBinder},
    rustc::{self},
};

// type AliasTyKey = (DefId, Vec<GenericArg>);
// type AliasTyKey = AliasTy;
type AliasTyKey = String;

impl AliasTy {
    fn key(&self) -> AliasTyKey {
        // TODO:ALIASKEYHACK: super janky hack, Nico -- why is the plain hasher not working? Maybe List<GenericArg> is not *really* hashable?
        format!("{:?}", self)
        // without_constrs(&self)
        // let args = self.args.iter().map(|arg| arg.clone()).collect();
        // (self.def_id, args)
    }
}

struct ProjectionTable<'sess, 'tcx> {
    genv: &'sess GlobalEnv<'sess, 'tcx>,
    def_id: DefId,
    // preds: FxHashMap<AliasTy, Ty>,
    preds: FxHashMap<AliasTyKey, Ty>,
}

impl<'sess, 'tcx> ProjectionTable<'sess, 'tcx> {
    fn new<T: TypeVisitable>(
        genv: &'sess GlobalEnv<'sess, 'tcx>,
        def_id: DefId,
        t: &T,
        span: Span,
    ) -> Result<Self, QueryErr> {
        let mut preds = FxHashMap::default();

        let mut gps = vec![];
        // 1. Insert generic predicates of the callsite `def_id`
        gps.push(genv.predicates_of(def_id)?.skip_binder());
        // 2. Insert generic predicates of the opaque-types
        let opaque_dids = opaque_def_ids(t);

        for did in opaque_dids.iter() {
            gps.push(genv.item_bounds(*did, span)?.skip_binder());
        }

        for predicates in gps {
            for pred in &predicates.predicates {
                if pred.kind.vars().is_empty() {
                    if let ClauseKind::Projection(proj_pred) = pred.kind.clone().skip_binder() {
                        match preds.insert(proj_pred.alias_ty.key(), proj_pred.term) {
                            None => (),
                            Some(_) => bug!("duplicate projection predicate"),
                        }
                    }
                }
            }
        }
        Ok(ProjectionTable { genv, def_id, preds })
    }

    fn normalize_with_preds(&self, alias_ty: &AliasTy) -> Option<Ty> {
        let alias_ty = without_constrs(alias_ty);
        let key = alias_ty.key();
        let res = self.preds.get(&key).cloned();
        // TODO:ALIASKEYHACK (uncomment below to see the mysterious key that doesn't get found in impl_trait02.rs)
        res
    }

    fn normalize_with_impl(&self, alias_ty: &AliasTy) -> Option<Ty> {
        let param_env = self.genv.tcx.param_env(self.def_id);
        Some(normalize_with_impl(self.genv, param_env, alias_ty))
    }

    fn normalize_projection(&self, alias_ty: &AliasTy) -> Ty {
        self.normalize_with_preds(alias_ty)
            .or_else(|| self.normalize_with_impl(alias_ty))
            .unwrap_or_else(|| {
                let def_id = self.def_id;
                bug!("failed to resolve {alias_ty:?} in {def_id:?}")
            })
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

struct OpaquesVisitor(FxHashSet<DefId>);

impl TypeVisitor for OpaquesVisitor {
    fn visit_bty(&mut self, bty: &BaseTy) -> ControlFlow<!, ()> {
        if let BaseTy::Alias(AliasKind::Opaque, alias_ty) = bty {
            let _ = self.0.insert(alias_ty.def_id);
            alias_ty.args.visit_with(self);
        }
        bty.super_visit_with(self)
    }
}

fn opaque_def_ids<T: TypeVisitable>(t: &T) -> FxHashSet<DefId> {
    let mut visitor = OpaquesVisitor(FxHashSet::default());
    t.visit_with(&mut visitor);
    visitor.0
}

// -----------------------------------------------------------------------------------------------------
// Code for normalizing `AliasTy` using impl -----------------------------------------------------------
// -----------------------------------------------------------------------------------------------------

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
        GenericArg::Const(_) => todo!(),
    }
}

fn into_rustc_bty<'tcx>(tcx: &TyCtxt<'tcx>, bty: &BaseTy) -> rustc_middle::ty::Ty<'tcx> {
    match bty {
        BaseTy::Int(i) => rustc_middle::ty::Ty::new_int(*tcx, *i), // rustc_middle::ty::Ty::mk_int(*tcx, int_ty),
        BaseTy::Uint(i) => rustc_middle::ty::Ty::new_uint(*tcx, *i),
        BaseTy::Param(pty) => pty.to_ty(*tcx),
        BaseTy::Slice(ty) => rustc_middle::ty::Ty::new_slice(*tcx, into_rustc_ty(tcx, ty)),
        BaseTy::Bool => rustc_middle::ty::Ty::new(*tcx, rustc_middle::ty::TyKind::Bool),
        BaseTy::Char => rustc_middle::ty::Ty::new(*tcx, rustc_middle::ty::TyKind::Char),
        BaseTy::Str => tcx.types.str_,
        BaseTy::Adt(adt_def, substs) => {
            let did = adt_def.did();
            let adt_def = tcx.adt_def(did);
            let substs = substs.iter().map(|arg| into_rustc_generic_arg(tcx, arg));
            let substs = tcx.mk_args_from_iter(substs);
            rustc_middle::ty::Ty::new_adt(*tcx, adt_def, substs)
        }
        BaseTy::Float(f) => rustc_middle::ty::Ty::new_float(*tcx, *f),
        BaseTy::RawPtr(_, _) => todo!(),
        BaseTy::Ref(_, _, _) => todo!(),
        BaseTy::Tuple(tys) => {
            let ts = tys.iter().map(|ty| into_rustc_ty(tcx, ty)).collect_vec();
            rustc_middle::ty::Ty::new_tup(*tcx, &ts)
        }
        BaseTy::Array(_, _) => todo!(),
        BaseTy::Never => todo!(),
        BaseTy::Closure(_, _) => todo!(),
        BaseTy::Generator(def_id, args) => {
            todo!("Generator {:?} {:?}", def_id, args)
            // let args = args.iter().map(|ty| into_rustc_ty(tcx, ty));
            // let args = tcx.mk_args_from_iter(args);
            // rustc_middle::ty::Ty::new_generator(*tcx, *def_id, args, mov)
        }
        BaseTy::GeneratorWitness(_) => todo!(),
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
struct TVarSubst {
    map: FxHashMap<ParamTy, Ty>,
}

impl TVarSubst {
    fn mk_subst(src: &rustc_middle::ty::Ty, dst: &Ty) -> Vec<GenericArg> {
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

    fn infer_from_arg(&mut self, src: &rustc_middle::ty::GenericArg, dst: &GenericArg) {
        if let GenericArg::Ty(dst) = dst {
            self.infer_from_ty(&src.as_type().unwrap(), dst);
        }
    }

    fn infer_from_ty(&mut self, src: &rustc_middle::ty::Ty, dst: &Ty) {
        use rustc_middle::ty;
        match src.kind().clone() {
            ty::TyKind::Param(pty) => self.insert(&pty, dst),
            ty::TyKind::Adt(_, src_subst) => {
                // NOTE: see https://github.com/flux-rs/flux/pull/478#issuecomment-1650983695
                if let Some(dst) = dst.as_bty_skipping_existentials() &&
                   !dst.has_escaping_bvars() &&
                   let BaseTy::Adt(_, dst_subst) = dst.clone()
                   {
                        debug_assert_eq!(src_subst.len(), dst_subst.len());
                        iter::zip(src_subst, &dst_subst)
                            .for_each(|(src_arg, dst_arg)| self.infer_from_arg(&src_arg, dst_arg));
                   } else {
                        bug!("unexpected base_ty");
                   }
            }
            ty::TyKind::Array(src, _) => {
                if let Some(BaseTy::Array(dst, _)) = dst.as_bty_skipping_existentials() {
                    self.infer_from_ty(&src, dst);
                } else {
                    bug!("unexpected base_ty");
                }
            }

            ty::TyKind::Slice(src) => {
                if let Some(BaseTy::Slice(dst)) = dst.as_bty_skipping_existentials() {
                    self.infer_from_ty(&src, dst);
                } else {
                    bug!("unexpected base_ty");
                }
            }
            ty::TyKind::Tuple(src_tys) => {
                if let Some(BaseTy::Tuple(dst_tys)) = dst.as_bty_skipping_existentials() {
                    debug_assert_eq!(src_tys.len(), dst_tys.len());
                    iter::zip(src_tys.iter(), dst_tys.iter())
                        .for_each(|(src, dst)| self.infer_from_ty(&src, dst));
                } else {
                    bug!("unexpected base_ty");
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
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
) -> ImplSourceUserDefinedData<'tcx, Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>> {
    // 1a. build up the `Obligation` query
    let trait_def_id = genv.tcx.parent(elem);
    let trait_ref = TraitRef::new(genv.tcx, trait_def_id, vec![into_rustc_ty(&genv.tcx, impl_rty)]);
    let predicate = trait_ref.to_predicate(genv.tcx);

    let oblig = Obligation {
        cause: ObligationCause::dummy(), // TODO(RJ): use with_span instead of `dummy`
        param_env,
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

/// QUERY: normalize <std::vec::IntoIter<Nat> as std::iter::Iterator::Item>
/// Given an an `impl_rty` e.g. `std::vec::IntoIter<Nat>` and an `elem` e.g. `std::iter::Iterator::Item`,
/// returns the component of the `impl_rty` that corresponds to the `elem`, e.g. `Nat`.

fn normalize_with_impl<'tcx>(
    genv: &GlobalEnv<'_, 'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    alias_ty: &AliasTy,
) -> Ty {
    let GenericArg::Ty(impl_rty) = &alias_ty.args[0] else { bug!("unexpected {alias_ty:?}") };
    let elem = alias_ty.def_id;

    // 1. Use elem == Trait::Item to find the impl-block corresponding to the implementation of `Trait` for the `impl_rty`
    let impl_source = get_impl_source(genv, elem, impl_rty, param_env);

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
    let impl_ty = genv.tcx.type_of(impl_id).instantiate_identity();
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
        .args[0]
        .as_type()
        .unwrap();
    let generics = TVarSubst::mk_subst(&src, impl_rty);

    // 5. Apply the `generics` substitution to the `impl_ty` to get the "resolved" `elem` type
    EarlyBinder(impl_ty).instantiate(&generics, &[])
}

// -----------------------------------------------------------------------------------------------------
// Type folder that recursively normalizes all nested `AliasTy` e.g. in a `FnSig`
// -----------------------------------------------------------------------------------------------------

impl<'sess, 'tcx> TypeFolder for ProjectionTable<'sess, 'tcx> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Alias(AliasKind::Projection, alias_ty), _idx) => {
                // TODO(RJ): ignoring the idx -- but shouldn't `Projection` be a TyKind and not in BaseTy?
                self.normalize_projection(alias_ty)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

pub fn normalize<'sess, T: TypeFoldable + TypeVisitable + Clone>(
    genv: &'sess GlobalEnv<'sess, '_>,
    def_id: DefId,
    t: &T,
    span: Span,
) -> Result<T, QueryErr> {
    // add opaques to table then normalize_from_preds will "just work"?
    let mut table = ProjectionTable::new(genv, def_id, t, span)?;
    Ok(t.fold_with(&mut table))
}
