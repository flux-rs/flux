use std::iter;

#[allow(unused_imports)]
use flux_common::bug;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::InferCtxt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSource, ObligationCause},
    ty::{EarlyBoundRegion, ParamTy, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    fold::{FallibleTypeFolder, TypeSuperFoldable},
    AliasKind, AliasPred, AliasTy, BaseTy, BoundRegion, Clause, ClauseKind, Expr, ExprKind,
    GenericArg, GenericArgs, ProjectionPredicate, RefineArgs, Region, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::fold::TypeVisitable,
    rustc::ty::FreeRegion,
};

pub(crate) struct Normalizer<'genv, 'tcx, 'cx> {
    genv: GlobalEnv<'genv, 'tcx>,
    selcx: SelectionContext<'cx, 'tcx>,
    def_id: DefId,
    param_env: Vec<Clause>,
}

impl<'genv, 'tcx, 'cx> Normalizer<'genv, 'tcx, 'cx> {
    pub(crate) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        infcx: &'cx InferCtxt<'tcx>,
        callsite_def_id: DefId,
        refine_params: &[Expr],
    ) -> QueryResult<Self> {
        let param_env = genv
            .predicates_of(callsite_def_id)?
            .instantiate_identity(genv, refine_params)?;
        let selcx = SelectionContext::new(infcx);
        Ok(Normalizer { genv, selcx, def_id: callsite_def_id, param_env })
    }

    fn normalize_alias_pred(
        &mut self,
        alias_pred: &AliasPred,
        refine_args: &RefineArgs,
    ) -> QueryResult<Expr> {
        if let Some(impl_id) = self.impl_id_of_alias_ty(alias_pred)? {
            let pred = self
                .genv
                .assoc_predicate_def(impl_id, alias_pred.name)?
                .instantiate(&alias_pred.args, &[]);
            let expr = pred.replace_bound_exprs(refine_args);
            Ok(expr)
        } else {
            Ok(Expr::alias_pred(alias_pred.clone(), refine_args.clone()))
        }
    }

    fn normalize_projection_ty(&mut self, obligation: &AliasTy) -> QueryResult<Ty> {
        let mut candidates = vec![];
        self.assemble_candidates_from_param_env(obligation, &mut candidates);
        self.assemble_candidates_from_trait_def(obligation, &mut candidates)?;
        self.assemble_candidates_from_impls(obligation, &mut candidates)?;

        if candidates.is_empty() {
            return Ok(Ty::alias(AliasKind::Projection, obligation.clone()));
        }
        if candidates.len() > 1 {
            bug!("ambiguity when resolving `{obligation:?}` in {:?}", self.def_id);
        }
        self.confirm_candidate(candidates.pop().unwrap(), obligation)
    }

    fn confirm_candidate(&self, candidate: Candidate, obligation: &AliasTy) -> QueryResult<Ty> {
        match candidate {
            Candidate::ParamEnv(pred) | Candidate::TraitDef(pred) => Ok(pred.term),
            Candidate::UserDefinedImpl(impl_def_id) => {
                // Given a projection obligation
                //     <IntoIter<{v. i32[v] | v > 0}, Global> as Iterator>::Item
                // and the id of a rust impl block
                //     impl<T, A: Allocator> Iterator for IntoIter<T, A>

                // 1. Match the self type of the rust impl block and the flux self type of the obligation
                //    to infer a substitution
                //        IntoIter<{v. i32[v] | v > 0}, Global> against IntoIter<T, A>
                //            => {T -> {v. i32[v] | v > 0}, A -> Global}
                let impl_trait_ref = self
                    .tcx()
                    .impl_trait_ref(impl_def_id)
                    .unwrap()
                    .skip_binder();

                let generics = self.tcx().generics_of(impl_def_id);

                let mut subst = TVarSubst::new(generics);
                subst.infer_from_args(impl_trait_ref.args, &obligation.args);
                let args = subst.finish(self.tcx(), generics);

                // 2. Get the associated type in the impl block and apply the substitution to it
                let assoc_type_id = self
                    .tcx()
                    .associated_items(impl_def_id)
                    .in_definition_order()
                    .find(|item| item.trait_item_def_id == Some(obligation.def_id))
                    .map(|item| item.def_id)
                    .unwrap();

                Ok(self
                    .genv
                    .type_of(assoc_type_id)?
                    .instantiate(&args, &[])
                    .into_ty())
            }
        }
    }

    fn assemble_candidates_from_param_env(
        &self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) {
        assemble_candidates_from_predicates(
            &self.param_env,
            obligation,
            Candidate::ParamEnv,
            candidates,
        );
    }

    fn assemble_candidates_from_trait_def(
        &self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) -> QueryResult<()> {
        let TyKind::Alias(AliasKind::Opaque, alias_ty) = obligation.self_ty().kind() else {
            return Ok(());
        };
        let bounds = self
            .genv
            .item_bounds(alias_ty.def_id)?
            .instantiate(&alias_ty.args, &alias_ty.refine_args);

        assemble_candidates_from_predicates(&bounds, obligation, Candidate::TraitDef, candidates);
        Ok(())
    }

    fn impl_id_of_alias_ty(&mut self, alias_pred: &AliasPred) -> QueryResult<Option<DefId>> {
        let trait_pred = Obligation::with_depth(
            self.tcx(),
            ObligationCause::dummy(),
            5,
            self.rustc_param_env(),
            into_rustc_trait_ref(self.tcx(), alias_pred),
        );
        match self.selcx.select(&trait_pred) {
            Ok(Some(ImplSource::UserDefined(impl_data))) => Ok(Some(impl_data.impl_def_id)),
            Ok(_) => Ok(None),
            Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
        }
    }

    fn assemble_candidates_from_impls(
        &mut self,
        obligation: &AliasTy,
        candidates: &mut Vec<Candidate>,
    ) -> QueryResult<()> {
        let trait_pred = Obligation::with_depth(
            self.tcx(),
            ObligationCause::dummy(),
            5,
            self.rustc_param_env(),
            into_rustc_alias_ty(self.tcx(), obligation).trait_ref(self.tcx()),
        );
        match self.selcx.select(&trait_pred) {
            Ok(Some(ImplSource::UserDefined(impl_data))) => {
                candidates.push(Candidate::UserDefinedImpl(impl_data.impl_def_id));
            }
            Ok(_) => (),
            Err(e) => bug!("error selecting {trait_pred:?}: {e:?}"),
        }
        Ok(())
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.selcx.tcx()
    }

    fn rustc_param_env(&self) -> rustc_middle::ty::ParamEnv<'tcx> {
        self.selcx.tcx().param_env(self.def_id)
    }
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

impl FallibleTypeFolder for Normalizer<'_, '_, '_> {
    type Error = QueryErr;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, Self::Error> {
        match ty.kind() {
            TyKind::Alias(AliasKind::Projection, alias_ty) => {
                self.normalize_projection_ty(alias_ty)
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, Self::Error> {
        if let ExprKind::AliasPred(alias_pred, refine_args) = expr.kind() {
            self.normalize_alias_pred(alias_pred, refine_args)
        } else {
            expr.try_super_fold_with(self)
        }
    }
}

#[derive(Debug)]
pub enum Candidate {
    UserDefinedImpl(DefId),
    ParamEnv(ProjectionPredicate),
    TraitDef(ProjectionPredicate),
}

pub fn into_rustc_trait_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    alias_pred: &AliasPred,
) -> rustc_middle::ty::TraitRef<'tcx> {
    let trait_def_id = alias_pred.trait_id;
    let args = into_rustc_generic_args(tcx, &alias_pred.args)
        .truncate_to(tcx, tcx.generics_of(trait_def_id));
    rustc_middle::ty::TraitRef::new(tcx, trait_def_id, args)
}

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
    rustc_middle::ty::AliasTy::new(
        tcx,
        alias_ty.def_id,
        into_rustc_generic_args(tcx, &alias_ty.args),
    )
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
        BaseTy::Coroutine(def_id, resume_ty, upvars) => {
            todo!("Generator {def_id:?} {resume_ty:?} {upvars:?}")
            // let args = args.iter().map(|arg| into_rustc_generic_arg(tcx, arg));
            // let args = tcx.mk_args_from_iter(args);
            // ty::Ty::new_generator(*tcx, *def_id, args, mov)
        }
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
        Region::ReFree(FreeRegion { scope, bound_region }) => {
            rustc_middle::ty::Region::new_free(tcx, scope, bound_region)
        }
    }
}

fn into_rustc_bound_region(bound_region: BoundRegion) -> rustc_middle::ty::BoundRegion {
    rustc_middle::ty::BoundRegion { var: bound_region.var, kind: bound_region.kind }
}

#[derive(Debug)]
struct TVarSubst {
    args: Vec<Option<GenericArg>>,
}

impl TVarSubst {
    fn new(generics: &rustc_middle::ty::Generics) -> Self {
        Self { args: vec![None; generics.count()] }
    }

    fn finish<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        generics: &'tcx rustc_middle::ty::Generics,
    ) -> Vec<GenericArg> {
        self.args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| {
                if let Some(arg) = arg {
                    arg
                } else {
                    let param = generics.param_at(idx, tcx);
                    bug!("cannot infer substitution for param {param:?}");
                }
            })
            .collect()
    }

    fn insert_param_ty(&mut self, pty: ParamTy, ty: &Ty) {
        let arg = GenericArg::Ty(ty.clone());
        if self.args[pty.index as usize].replace(arg).is_some() {
            bug!("duplicate insert");
        }
    }

    fn insert_early_bound_region(&mut self, ebr: EarlyBoundRegion, re: Region) {
        let arg = GenericArg::Lifetime(re);
        if self.args[ebr.index as usize].replace(arg).is_some() {
            bug!("duplicate insert");
        }
    }

    fn infer_from_args(&mut self, src: rustc_middle::ty::GenericArgsRef, dst: &GenericArgs) {
        debug_assert_eq!(src.len(), dst.len());
        for (src, dst) in iter::zip(src, dst) {
            self.infer_from_arg(src, dst);
        }
    }

    fn infer_from_arg(&mut self, src: rustc_middle::ty::GenericArg, dst: &GenericArg) {
        match dst {
            GenericArg::Ty(dst) => {
                self.infer_from_ty(&src.as_type().unwrap(), dst);
            }
            GenericArg::Lifetime(dst) => self.infer_from_region(&src.as_region().unwrap(), dst),
            _ => (),
        }
    }

    fn infer_from_ty(&mut self, src: &rustc_middle::ty::Ty, dst: &Ty) {
        use rustc_middle::ty;
        match src.kind() {
            ty::TyKind::Param(pty) => self.insert_param_ty(*pty, dst),
            ty::TyKind::Adt(_, src_subst) => {
                // NOTE: see https://github.com/flux-rs/flux/pull/478#issuecomment-1650983695
                if let Some(dst) = dst.as_bty_skipping_existentials()
                    && !dst.has_escaping_bvars()
                    && let BaseTy::Adt(_, dst_subst) = dst
                {
                    debug_assert_eq!(src_subst.len(), dst_subst.len());
                    for (src_arg, dst_arg) in iter::zip(*src_subst, dst_subst) {
                        self.infer_from_arg(src_arg, dst_arg);
                    }
                } else {
                    bug!("unexpected type {dst:?}");
                }
            }
            ty::TyKind::Array(src, _) => {
                if let Some(BaseTy::Array(dst, _)) = dst.as_bty_skipping_existentials() {
                    self.infer_from_ty(src, dst);
                } else {
                    bug!("unexpected type {dst:?}");
                }
            }
            ty::TyKind::Slice(src) => {
                if let Some(BaseTy::Slice(dst)) = dst.as_bty_skipping_existentials() {
                    self.infer_from_ty(src, dst);
                } else {
                    bug!("unexpected type {dst:?}");
                }
            }
            ty::TyKind::Tuple(src_tys) => {
                if let Some(BaseTy::Tuple(dst_tys)) = dst.as_bty_skipping_existentials() {
                    debug_assert_eq!(src_tys.len(), dst_tys.len());
                    iter::zip(src_tys.iter(), dst_tys.iter())
                        .for_each(|(src, dst)| self.infer_from_ty(&src, dst));
                } else {
                    bug!("unexpected type {dst:?}");
                }
            }
            ty::TyKind::Ref(src_re, src_ty, _) => {
                if let Some(BaseTy::Ref(dst_re, dst_ty, _)) = dst.as_bty_skipping_existentials() {
                    self.infer_from_region(src_re, dst_re);
                    self.infer_from_ty(src_ty, dst_ty);
                } else {
                    bug!("unexpected type {dst:?}");
                }
            }
            _ => {}
        }
    }

    fn infer_from_region(&mut self, src: &rustc_middle::ty::Region, dst: &Region) {
        if let rustc_middle::ty::RegionKind::ReEarlyBound(ebr) = src.kind() {
            self.insert_early_bound_region(ebr, *dst);
        }
    }
}
