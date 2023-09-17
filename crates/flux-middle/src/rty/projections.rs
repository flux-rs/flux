use std::iter;

#[allow(unused_imports)]
use flux_common::bug;
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::TyCtxtInferExt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSource, ImplSourceUserDefinedData, ObligationCause},
    ty::{ParamTy, ToPredicate, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable},
    AliasKind, AliasTy, BaseTy, BoundRegion, Clause, ClauseKind, Expr, GenericArg,
    ProjectionPredicate, Region, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    intern::List,
    queries::{QueryErr, QueryResult},
    rty::{fold::TypeVisitable, EarlyBinder},
    rustc::{
        self,
        ty::{BoundRegionKind, FreeRegion},
    },
};

type AliasTyKey = String;

impl AliasTy {
    fn key(&self) -> AliasTyKey {
        // TODO:ALIASKEYHACK: super janky hack, Nico -- why is the plain hasher not working? Maybe List<GenericArg> is not *really* hashable?
        format!("{:?}", self)
    }
}

struct ProjectionTable<'sess, 'tcx> {
    genv: &'sess GlobalEnv<'sess, 'tcx>,
    def_id: DefId,
    preds: UnordMap<AliasTyKey, Ty>,
    param_env: List<Clause>,
}

impl<'sess, 'tcx> ProjectionTable<'sess, 'tcx> {
    fn new<T: TypeVisitable>(
        genv: &'sess GlobalEnv<'sess, 'tcx>,
        src_def_id: DefId,
        param_env: List<Clause>,
        t: &T,
    ) -> QueryResult<Self> {
        let mut preds = UnordMap::default();

        let mut vec = vec![];
        // 1. Insert generic predicates of the callsite `callsite_def_id`
        // TODO-EARLY vec.push(genv.predicates_of(callsite_def_id)?.skip_binder().predicates);
        vec.push(param_env.clone());
        // 2. Insert generic predicates of the opaque-types
        for (opaque_def_id, (args, refine_args)) in t.opaque_refine_args() {
            vec.push(
                genv.item_bounds(opaque_def_id)?
                    .instantiate(&args, &refine_args),
            );
        }

        for clauses in vec {
            for pred in &clauses {
                if let ClauseKind::Projection(proj_pred) = pred.kind() {
                    match preds.insert(proj_pred.projection_ty.key(), proj_pred.term) {
                        None => (),
                        Some(_) => bug!("duplicate projection predicate"),
                    }
                }
            }
        }
        Ok(ProjectionTable { genv, def_id: src_def_id, param_env, preds })
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

// -----------------------------------------------------------------------------------------------------
// Code for normalizing `AliasTy` using impl -----------------------------------------------------------
// -----------------------------------------------------------------------------------------------------

fn into_rustc_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: &[GenericArg],
) -> rustc_middle::ty::GenericArgsRef<'tcx> {
    tcx.mk_args_from_iter(args.iter().map(|arg| into_rustc_generic_arg(tcx, arg)))
}

fn into_rustc_generic_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    arg: &GenericArg,
) -> rustc_middle::ty::GenericArg<'tcx> {
    use rustc_middle::ty;
    match arg {
        GenericArg::Ty(ty) => ty::GenericArg::from(into_rustc_ty(tcx, ty)),
        GenericArg::BaseTy(bty) => {
            ty::GenericArg::from(into_rustc_ty(tcx, &bty.clone().skip_binder()))
        }
        GenericArg::Lifetime(re) => ty::GenericArg::from(into_rustc_region(tcx, *re)),
        GenericArg::Const(_) => todo!(),
    }
}

fn into_rustc_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty) -> rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Indexed(bty, _) => into_rustc_bty(tcx, bty),
        TyKind::Exists(ty) => into_rustc_ty(tcx, &ty.clone().skip_binder()),
        TyKind::Constr(_, ty) => into_rustc_ty(tcx, ty),
        TyKind::Param(pty) => pty.to_ty(tcx),
        TyKind::Alias(kind, alias_ty) => {
            rustc_middle::ty::Ty::new_alias(
                tcx,
                into_rustc_alias_kind(kind),
                into_rustc_alias_ty(tcx, alias_ty),
            )
        }
        TyKind::Uninit
        | TyKind::Ptr(_, _)
        | TyKind::Discr(_, _)
        | TyKind::Downcast(_, _, _, _, _)
        | TyKind::Blocked(_) => bug!(),
    }
}

fn into_rustc_alias_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    alias_ty: &AliasTy,
) -> rustc_middle::ty::AliasTy<'tcx> {
    tcx.mk_alias_ty(alias_ty.def_id, into_rustc_generic_args(tcx, &alias_ty.args))
}

fn into_rustc_alias_kind(kind: &AliasKind) -> rustc_middle::ty::AliasKind {
    use rustc_middle::ty;
    match kind {
        AliasKind::Opaque => ty::AliasKind::Opaque,
        AliasKind::Projection => ty::AliasKind::Projection,
    }
}

fn into_rustc_bty<'tcx>(tcx: TyCtxt<'tcx>, bty: &BaseTy) -> rustc_middle::ty::Ty<'tcx> {
    use rustc_middle::ty;
    match bty {
        BaseTy::Int(i) => ty::Ty::new_int(tcx, *i),
        BaseTy::Uint(i) => ty::Ty::new_uint(tcx, *i),
        BaseTy::Param(pty) => pty.to_ty(tcx),
        BaseTy::Slice(ty) => ty::Ty::new_slice(tcx, into_rustc_ty(tcx, ty)),
        BaseTy::Bool => tcx.types.bool,
        BaseTy::Char => tcx.types.char,
        BaseTy::Str => tcx.types.str_,
        BaseTy::Adt(adt_def, args) => {
            let did = adt_def.did();
            let adt_def = tcx.adt_def(did);
            let args = into_rustc_generic_args(tcx, args);
            ty::Ty::new_adt(tcx, adt_def, args)
        }
        BaseTy::Float(f) => ty::Ty::new_float(tcx, *f),
        BaseTy::RawPtr(ty, mutbl) => {
            ty::Ty::new_ptr(tcx, ty::TypeAndMut { ty: into_rustc_ty(tcx, ty), mutbl: *mutbl })
        }
        BaseTy::Ref(re, ty, mutbl) => {
            ty::Ty::new_ref(
                tcx,
                into_rustc_region(tcx, *re),
                ty::TypeAndMut { ty: into_rustc_ty(tcx, ty), mutbl: *mutbl },
            )
        }
        BaseTy::Tuple(tys) => {
            let ts = tys.iter().map(|ty| into_rustc_ty(tcx, ty)).collect_vec();
            ty::Ty::new_tup(tcx, &ts)
        }
        BaseTy::Array(_, _) => todo!(),
        BaseTy::Never => tcx.types.never,
        BaseTy::Closure(_, _) => todo!(),
        BaseTy::Generator(def_id, args) => {
            todo!("Generator {:?} {:?}", def_id, args)
            // let args = args.iter().map(|arg| into_rustc_generic_arg(tcx, arg));
            // let args = tcx.mk_args_from_iter(args);
            // ty::Ty::new_generator(*tcx, *def_id, args, mov)
        }
        BaseTy::GeneratorWitness(_) => todo!(),
    }
}

fn into_rustc_region(tcx: TyCtxt, re: Region) -> rustc_middle::ty::Region {
    match re {
        Region::ReLateBound(debruijn, bound_region) => {
            rustc_middle::ty::Region::new_late_bound(
                tcx,
                debruijn,
                into_rustc_bound_region(bound_region),
            )
        }
        Region::ReEarlyBound(ebr) => rustc_middle::ty::Region::new_early_bound(tcx, ebr),
        Region::ReStatic => tcx.lifetimes.re_static,
        Region::ReVar(rvid) => rustc_middle::ty::Region::new_var(tcx, rvid),
        Region::ReErased => tcx.lifetimes.re_erased,
        Region::ReFree(FreeRegion { scope, bound_region }) => {
            rustc_middle::ty::Region::new_free(
                tcx,
                scope,
                into_rustc_bound_region_kind(bound_region),
            )
        }
    }
}

fn into_rustc_bound_region_kind(
    bound_region: BoundRegionKind,
) -> rustc_middle::ty::BoundRegionKind {
    use rustc_middle::ty;
    match bound_region {
        BoundRegionKind::BrAnon => ty::BoundRegionKind::BrAnon(None),
        BoundRegionKind::BrNamed(def_id, sym) => ty::BoundRegionKind::BrNamed(def_id, sym),
        BoundRegionKind::BrEnv => ty::BoundRegionKind::BrEnv,
    }
}

fn into_rustc_bound_region(bound_region: BoundRegion) -> rustc_middle::ty::BoundRegion {
    rustc_middle::ty::BoundRegion {
        var: bound_region.var,
        kind: into_rustc_bound_region_kind(bound_region.kind),
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
    projection_ty: &rustc_middle::ty::AliasTy<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
) -> ImplSourceUserDefinedData<'tcx, Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>> {
    // 1a. build up the `Obligation` query
    let trait_ref = projection_ty.trait_ref(genv.tcx);
    let oblig = Obligation {
        cause: ObligationCause::dummy(), // TODO(RJ): use with_span instead of `dummy`
        param_env,
        predicate: trait_ref.to_predicate(genv.tcx),
        recursion_depth: 5, // TODO(RJ): made up a random number!
    };

    // 1b. build up the `SelectionContext`
    let infcx = genv.tcx.infer_ctxt().build();
    let mut selcx = SelectionContext::new(&infcx);

    // 1c. issue query to find the `impl` block that implements the `Trait`
    let impl_source = match selcx.select(&oblig) {
        Ok(Some(ImplSource::UserDefined(impl_source))) => impl_source,
        Ok(e) => bug!("invalid selection for {oblig:?} = {e:?}"),
        Err(e) => bug!("error selecting {oblig:?}: {e:?}"),
    };
    impl_source
}

/// QUERY: normalize `<std::vec::IntoIter<Nat> as std::iter::Iterator::Item>`
/// Given an an `impl_rty` e.g. `std::vec::IntoIter<Nat>` and an `elem` e.g. `std::iter::Iterator::Item`,
/// returns the component of the `impl_rty` that corresponds to the `elem`, e.g. `Nat`.
fn normalize_with_impl<'tcx>(
    genv: &GlobalEnv<'_, 'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    alias_ty: &AliasTy,
) -> Ty {
    let projection_ty = into_rustc_alias_ty(genv.tcx, alias_ty);

    // 1. Use elem == Trait::Item to find the impl-block corresponding to the implementation of `Trait` for the `impl_rty`
    let impl_source = get_impl_source(genv, &projection_ty, param_env);

    // 2. Extract the `DefId` corresponding to `elem` from the impl-block
    // TODO(RJ): is there a faster way to get the def_id of an associated item from an impl?
    let impl_id = genv
        .tcx
        .associated_items(impl_source.impl_def_id)
        .in_definition_order()
        .find(|item| item.trait_item_def_id == Some(alias_ty.def_id))
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
    let generics = TVarSubst::mk_subst(&src, alias_ty.self_ty());

    // 5. Apply the `generics` substitution to the `impl_ty` to get the "resolved" `elem` type
    EarlyBinder(impl_ty).instantiate(&generics, &[])
}

// -----------------------------------------------------------------------------------------------------
// Type folder that recursively normalizes all nested `AliasTy` e.g. in a `FnSig`
// -----------------------------------------------------------------------------------------------------

impl<'sess, 'tcx> FallibleTypeFolder for ProjectionTable<'sess, 'tcx> {
    type Error = QueryErr;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, Self::Error> {
        if let TyKind::Alias(AliasKind::Projection, alias_ty) = ty.kind() {
            normalize_projection_ty(self.genv, self.def_id, &self.param_env, alias_ty)
            // self.normalize_projection(alias_ty)
        } else {
            ty.try_super_fold_with(self)
        }
    }
}

pub fn normalize<'sess, T: TypeFoldable + TypeVisitable + Clone>(
    genv: &'sess GlobalEnv<'sess, '_>,
    callsite_def_id: DefId,
    src_params: &[Expr],
    t: &T,
) -> QueryResult<T> {
    let param_env = List::from(
        genv.predicates_of(callsite_def_id)?
            .instantiate_identity(genv, src_params)?,
    );

    let mut table = ProjectionTable::new(genv, callsite_def_id, param_env, t)?;
    t.try_fold_with(&mut table)
}

pub enum Candidate {
    // UserDefinedImpl(DefId),
    ParamEnv(ProjectionPredicate),
    TraitDef(ProjectionPredicate),
}

fn normalize_projection_ty(
    genv: &GlobalEnv,
    callsite_def_id: DefId,
    param_env: &[Clause],
    obligation: &AliasTy,
) -> QueryResult<Ty> {
    let mut candidates = vec![];
    assemble_candidates_from_param_env(param_env, obligation, &mut candidates);
    assemble_candidates_from_trait_def(genv, obligation, &mut candidates)?;
    assemble_candidates_from_impls(genv, callsite_def_id, obligation, &mut candidates)?;

    match &candidates[..] {
        [Candidate::ParamEnv(pred) | Candidate::TraitDef(pred)] => Ok(pred.term.clone()),
        [] => bug!("failed to resolve `{obligation:?}` in {callsite_def_id:?}"),
        [_, _, ..] => bug!("ambiguity when resolving `{obligation:?}` in {callsite_def_id:?}"),
    }
}

fn assemble_candidates_from_param_env(
    param_env: &[Clause],
    obligation: &AliasTy,
    candidates: &mut Vec<Candidate>,
) {
    assemble_candidates_from_predicates(param_env, obligation, Candidate::ParamEnv, candidates);
}

fn assemble_candidates_from_trait_def(
    genv: &GlobalEnv,
    obligation: &AliasTy,
    candidates: &mut Vec<Candidate>,
) -> QueryResult<()> {
    let TyKind::Alias(AliasKind::Opaque, alias_ty) = obligation.self_ty().kind() else {
        return Ok(());
    };
    let bounds = genv
        .item_bounds(alias_ty.def_id)?
        .instantiate(&alias_ty.args, &alias_ty.refine_args);

    assemble_candidates_from_predicates(&bounds, obligation, Candidate::TraitDef, candidates);
    Ok(())
}

fn assemble_candidates_from_impls(
    genv: &GlobalEnv,
    callsite_def_id: DefId,
    obligation: &AliasTy,
    candidates: &mut Vec<Candidate>,
) -> QueryResult<()> {
    // Given `<someType as SomeTrait>::SomeItem`

    // 1. Check if there is a `impl SomeType for SomeTrait`
    let infcx = genv.tcx.infer_ctxt().build();
    let mut selcx = SelectionContext::new(&infcx);
    let trait_ref = Obligation {
        cause: ObligationCause::dummy(),
        param_env: genv.tcx.param_env(callsite_def_id),
        predicate: into_rustc_alias_ty(genv.tcx, obligation)
            .trait_ref(genv.tcx)
            .to_predicate(genv.tcx),
        recursion_depth: 5,
    };
    let impl_data = match selcx.select(&trait_ref) {
        Ok(Some(ImplSource::UserDefined(impl_data))) => impl_data,
        Ok(_) => return Ok(()),
        Err(e) => bug!("error selecting {trait_ref:?}: {e:?}"),
    };

    // 2. Get the associated item id for the impl block
    let assoc_item_id = genv
        .tcx
        .associated_items(impl_data.impl_def_id)
        .in_definition_order()
        .find(|item| item.trait_item_def_id == Some(obligation.def_id))
        .map(|item| item.def_id)
        .unwrap();

    // 3. Compute the rty::Ty for `impl_id`
    // let impl_ty = genv.tcx.type_of(assoc_item_id).instantiate_identity();
    // let impl_ty = rustc::lowering::lower_ty(genv.tcx, impl_ty).unwrap();
    // let impl_ty = genv
    //     .refine_default(&genv.generics_of(impl_source.impl_def_id).unwrap(), &impl_ty)
    //     .unwrap();

    println!("\n{callsite_def_id:?}\n{assoc_item_id:?}");
    println!("{impl_data:?}");

    Ok(())

    // todo!()
}

fn assemble_candidates_from_predicates(
    predicates: &[Clause],
    obligation: &AliasTy,
    ctor: fn(ProjectionPredicate) -> Candidate,
    candidates: &mut Vec<Candidate>,
) {
    for predicate in predicates {
        if let ClauseKind::Projection(pred) = predicate.kind() {
            if &pred.projection_ty == obligation {
                candidates.push(ctor(pred.clone()));
            }
        }
    }
}
