use std::iter;

#[allow(unused_imports)]
use flux_common::bug;
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::InferCtxt, traits::Obligation};
use rustc_middle::{
    traits::{ImplSource, ObligationCause},
    ty::{EarlyBoundRegion, ParamTy, TyCtxt},
};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    canonicalize::{CanonicalConstrTy, CanonicalTy},
    fold::{FallibleTypeFolder, TypeSuperFoldable},
    AliasKind, AliasReft, AliasTy, BaseTy, Clause, ClauseKind, Expr, ExprKind, GenericArg,
    GenericArgs, ProjectionPredicate, RefineArgs, Region, SubsetTy, Ty, TyKind,
};
use crate::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::fold::TypeVisitable,
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

    fn normalize_alias_reft(
        &mut self,
        obligation: &AliasReft,
        refine_args: &RefineArgs,
    ) -> QueryResult<Expr> {
        if let Some(impl_def_id) = self.impl_id_of_alias_reft(obligation)? {
            let impl_trait_ref = self
                .genv
                .impl_trait_ref(impl_def_id)?
                .unwrap()
                .skip_binder();
            let generics = self.tcx().generics_of(impl_def_id);

            let mut subst = Equate::new(generics);
            for (a, b) in iter::zip(&impl_trait_ref.args, &obligation.args) {
                subst.generic_args(a, b);
            }
            let args = subst.finish(self.tcx(), generics);

            let pred = self
                .genv
                .assoc_refinement_def(impl_def_id, obligation.name)?
                .instantiate(&args, &[]);
            let expr = pred.apply(refine_args);
            Ok(expr)
        } else {
            Ok(Expr::alias(obligation.clone(), refine_args.clone()))
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
                    .genv
                    .impl_trait_ref(impl_def_id)?
                    .unwrap()
                    .skip_binder();

                let generics = self.tcx().generics_of(impl_def_id);

                let mut subst = Equate::new(generics);
                for (a, b) in iter::zip(&impl_trait_ref.args, &obligation.args) {
                    subst.generic_args(a, b);
                }
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
                    .to_ty())
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
    ) -> QueryResult {
        if let GenericArg::Ty(ty) = &obligation.args[0]
            && let TyKind::Alias(AliasKind::Opaque, alias_ty) = ty.kind()
        {
            let bounds = self
                .genv
                .item_bounds(alias_ty.def_id)?
                .instantiate(&alias_ty.args, &alias_ty.refine_args);

            assemble_candidates_from_predicates(
                &bounds,
                obligation,
                Candidate::TraitDef,
                candidates,
            );
        }
        Ok(())
    }

    fn impl_id_of_alias_reft(&mut self, alias: &AliasReft) -> QueryResult<Option<DefId>> {
        let trait_pred = Obligation::with_depth(
            self.tcx(),
            ObligationCause::dummy(),
            5,
            self.rustc_param_env(),
            alias.to_rustc_trait_ref(self.tcx()),
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
    ) -> QueryResult {
        let trait_pred = Obligation::with_depth(
            self.tcx(),
            ObligationCause::dummy(),
            5,
            self.rustc_param_env(),
            obligation.to_rustc(self.tcx()).trait_ref(self.tcx()),
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
        if let ExprKind::Alias(alias_pred, refine_args) = expr.kind() {
            self.normalize_alias_reft(alias_pred, refine_args)
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

// #[derive(Debug)]
// struct TVarSubst {
//     args: Vec<Option<GenericArg>>,
// }

// impl TVarSubst {
//     fn new(generics: &rustc_middle::ty::Generics) -> Self {
//         Self { args: vec![None; generics.count()] }
//     }

//     fn finish<'tcx>(
//         self,
//         tcx: TyCtxt<'tcx>,
//         generics: &'tcx rustc_middle::ty::Generics,
//     ) -> Vec<GenericArg> {
//         self.args
//             .into_iter()
//             .enumerate()
//             .map(|(idx, arg)| {
//                 if let Some(arg) = arg {
//                     arg
//                 } else {
//                     let param = generics.param_at(idx, tcx);
//                     bug!("cannot infer substitution for param {param:?}");
//                 }
//             })
//             .collect()
//     }

//     fn insert_param_ty(&mut self, pty: ParamTy, ty: &Ty) {
//         let arg = GenericArg::Ty(ty.clone());
//         if self.args[pty.index as usize].replace(arg).is_some() {
//             bug!("duplicate insert");
//         }
//     }

//     fn insert_early_bound_region(&mut self, ebr: EarlyBoundRegion, re: Region) {
//         let arg = GenericArg::Lifetime(re);
//         if self.args[ebr.index as usize].replace(arg).is_some() {
//             bug!("duplicate insert");
//         }
//     }

//     fn infer_from_args(&mut self, src: rustc_middle::ty::GenericArgsRef, dst: &GenericArgs) {
//         debug_assert_eq!(src.len(), dst.len());
//         for (src, dst) in iter::zip(src, dst) {
//             self.infer_from_arg(src, dst);
//         }
//     }

//     fn infer_from_arg(&mut self, src: rustc_middle::ty::GenericArg, dst: &GenericArg) {
//         match dst {
//             GenericArg::Ty(dst) => {
//                 self.infer_from_ty(&src.as_type().unwrap(), dst);
//             }
//             GenericArg::Lifetime(dst) => self.infer_from_region(&src.as_region().unwrap(), dst),
//             GenericArg::Base(ty) => {
//                 // todo!()
//                 // self.infer_from_ty(&src.as_type().unwrap(), ty.bty_skipping_binder());
//             }
//             _ => (),
//         }
//     }

//     fn infer_from_ty(&mut self, src: &rustc_middle::ty::Ty, dst: &Ty) {
//         use rustc_middle::ty;
//         match src.kind() {
//             ty::TyKind::Param(pty) => {
//                 if !dst.has_escaping_bvars() {
//                     self.insert_param_ty(*pty, dst);
//                 }
//             }
//             ty::TyKind::Adt(_, src_subst) => {
//                 // NOTE: see https://github.com/flux-rs/flux/pull/478#issuecomment-1650983695
//                 if let Some(dst) = dst.as_bty_skipping_existentials()
//                     && let BaseTy::Adt(_, dst_subst) = dst
//                 {
//                     debug_assert_eq!(src_subst.len(), dst_subst.len());
//                     for (src_arg, dst_arg) in iter::zip(*src_subst, dst_subst) {
//                         self.infer_from_arg(src_arg, dst_arg);
//                     }
//                 } else {
//                     bug!("unexpected type {dst:?}");
//                 }
//             }
//             ty::TyKind::Array(src, _) => {
//                 if let Some(BaseTy::Array(dst, _)) = dst.as_bty_skipping_existentials() {
//                     self.infer_from_ty(src, dst);
//                 } else {
//                     bug!("unexpected type {dst:?}");
//                 }
//             }
//             ty::TyKind::Slice(src) => {
//                 if let Some(BaseTy::Slice(dst)) = dst.as_bty_skipping_existentials() {
//                     self.infer_from_ty(src, dst);
//                 } else {
//                     bug!("unexpected type {dst:?}");
//                 }
//             }
//             ty::TyKind::Tuple(src_tys) => {
//                 if let Some(BaseTy::Tuple(dst_tys)) = dst.as_bty_skipping_existentials() {
//                     debug_assert_eq!(src_tys.len(), dst_tys.len());
//                     iter::zip(src_tys.iter(), dst_tys.iter())
//                         .for_each(|(src, dst)| self.infer_from_ty(&src, dst));
//                 } else {
//                     bug!("unexpected type {dst:?}");
//                 }
//             }
//             ty::TyKind::Ref(src_re, src_ty, _) => {
//                 if let Some(BaseTy::Ref(dst_re, dst_ty, _)) = dst.as_bty_skipping_existentials() {
//                     self.infer_from_region(src_re, dst_re);
//                     self.infer_from_ty(src_ty, dst_ty);
//                 } else {
//                     bug!("unexpected type {dst:?}");
//                 }
//             }
//             _ => {}
//         }
//     }

//     fn infer_from_region(&mut self, src: &rustc_middle::ty::Region, dst: &Region) {
//         if let rustc_middle::ty::RegionKind::ReEarlyBound(ebr) = src.kind() {
//             self.insert_early_bound_region(ebr, *dst);
//         }
//     }
// }

#[derive(Debug)]
struct Equate {
    args: Vec<Option<GenericArg>>,
}

impl Equate {
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

    fn generic_args(&mut self, a: &GenericArg, b: &GenericArg) {
        match (a, b) {
            (GenericArg::Ty(a), GenericArg::Ty(b)) => self.tys(a, b),
            (GenericArg::Lifetime(a), GenericArg::Lifetime(b)) => self.regions(*a, *b),
            (GenericArg::Base(a), GenericArg::Base(b)) => {
                debug_assert_eq!(a.sort(), b.sort());
                self.btys(a.as_bty_skipping_binder(), b.as_bty_skipping_binder());
            }
            _ => {}
        }
    }

    fn tys(&mut self, a: &Ty, b: &Ty) {
        if let TyKind::Param(param_ty) = a.kind() {
            if !b.has_escaping_bvars() {
                self.insert_generic_arg(param_ty.index, GenericArg::Ty(b.clone()));
            }
            return;
        }
        let Some(a_bty) = a.as_bty_skipping_existentials() else { return };
        let Some(b_bty) = b.as_bty_skipping_existentials() else { return };
        self.btys(a_bty, b_bty);
    }

    fn btys(&mut self, a: &BaseTy, b: &BaseTy) {
        match (a, b) {
            (BaseTy::Param(_), _) => todo!(),
            (BaseTy::Adt(_, a_args), BaseTy::Adt(_, b_args)) => {
                debug_assert_eq!(a_args.len(), b_args.len());
                for (a_arg, b_arg) in iter::zip(a_args, b_args) {
                    self.generic_args(a_arg, b_arg);
                }
            }
            (BaseTy::Array(a_ty, _), BaseTy::Array(b_ty, _)) => {
                self.tys(a_ty, b_ty);
            }
            (BaseTy::Tuple(a_tys), BaseTy::Tuple(b_tys)) => {
                debug_assert_eq!(a_tys.len(), b_tys.len());
                for (a_ty, b_ty) in iter::zip(a_tys, b_tys) {
                    self.tys(a_ty, b_ty);
                }
            }
            (BaseTy::Ref(a_re, a_ty, _), BaseTy::Ref(b_re, b_ty, _)) => {
                self.regions(*a_re, *b_re);
                self.tys(a_ty, b_ty);
            }
            (BaseTy::Slice(a_ty), BaseTy::Slice(b_ty)) => {
                self.tys(a_ty, b_ty);
            }
            _ => {}
        }
    }

    fn regions(&mut self, a: Region, b: Region) {
        if let Region::ReEarlyBound(ebr) = a {
            self.insert_generic_arg(ebr.index, GenericArg::Lifetime(b));
        }
    }

    fn insert_generic_arg(&mut self, idx: u32, arg: GenericArg) {
        if self.args[idx as usize].replace(arg).is_some() {
            bug!("duplicate insert");
        }
    }
}
