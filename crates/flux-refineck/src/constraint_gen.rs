use std::iter;

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        self,
        evars::{EVarCxId, EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        AliasTy, BaseTy, BinOp, Binder, Const, Constraint, ESpan, EVarGen, EarlyBinder, Expr,
        ExprKind, FnOutput, GeneratorObligPredicate, GenericArg, GenericArgs, HoleKind, InferMode,
        Mutability, Path, PolyFnSig, PolyVariant, PtrKind, Ref, Sort, TupleTree, Ty, TyKind, Var,
    },
    rustc::mir::{BasicBlock, Place},
};
use itertools::{izip, Itertools};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::{LateBoundRegionConversionTime, RegionVariableOrigin::LateBoundRegion};
use rustc_middle::ty::Variance;
use rustc_span::Span;

use crate::{
    checker::errors::CheckerErrKind,
    fixpoint_encoding::KVarEncoding,
    refine_tree::{RefineCtxt, Scope, Snapshot},
    type_env::TypeEnv,
};

pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    def_id: DefId,
    refparams: &'a [Expr],
    kvar_gen: Box<dyn KVarGen + 'a>,
    span: Span,
}

pub(crate) struct Obligations {
    pub(crate) predicates: List<rty::Clause>,
    /// Snapshot of the refinement subtree where the obligations should be checked
    pub(crate) snapshot: Snapshot,
}

pub trait KVarGen {
    fn fresh(&mut self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr;
}

pub(crate) struct InferCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
    def_id: DefId,
    refparams: &'a [Expr],
    kvar_gen: &'a mut (dyn KVarGen + 'a),
    evar_gen: EVarGen,
    tag: Tag,
    scopes: FxIndexMap<EVarCxId, Scope>,
    obligs: Vec<rty::Clause>,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Tag {
    pub reason: ConstrReason,
    pub src_span: Span,
    pub dst_span: Option<ESpan>,
}

impl Tag {
    pub fn new(reason: ConstrReason, span: Span) -> Self {
        Self { reason, src_span: span, dst_span: None }
    }

    pub fn with_dst(self, dst_span: Option<ESpan>) -> Self {
        Self { dst_span, ..self }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum ConstrReason {
    Call,
    Assign,
    Ret,
    Fold,
    Assert(&'static str),
    Div,
    Rem,
    Goto(BasicBlock),
    Overflow,
    Other,
}

impl<'a, 'tcx> ConstrGen<'a, 'tcx> {
    pub fn new<G>(
        genv: &'a GlobalEnv<'a, 'tcx>,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'a [Expr],
        kvar_gen: G,
        span: Span,
    ) -> Self
    where
        G: KVarGen + 'a,
    {
        ConstrGen { genv, region_infcx, def_id, refparams, kvar_gen: Box::new(kvar_gen), span }
    }

    pub(crate) fn check_pred(
        &self,
        rcx: &mut RefineCtxt,
        pred: impl Into<Expr>,
        reason: ConstrReason,
    ) {
        rcx.check_pred(pred, Tag::new(reason, self.span));
    }

    pub(crate) fn subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty1: &Ty,
        ty2: &Ty,
        reason: ConstrReason,
    ) {
        let mut infcx = self.infcx(rcx, reason);
        let _ = infcx.subtyping(rcx, ty1, ty2);
        rcx.replace_evars(&infcx.solve().unwrap());
    }

    pub(crate) fn pack_closure_operands(
        &mut self,
        env: &mut TypeEnv,
        operands: &[Ty],
    ) -> Result<Vec<Ty>, CheckerErrKind> {
        let mut res = Vec::new();
        for ty in operands {
            let packed_ty = match ty.kind() {
                TyKind::Ptr(PtrKind::Shr(region), path) => {
                    let ty = env.get(path);
                    rty::Ty::mk_ref(*region, ty, Mutability::Not)
                }
                _ => ty.clone(),
            };
            res.push(packed_ty);
        }
        Ok(res)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_fn_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        callee_def_id: Option<DefId>,
        fn_sig: EarlyBinder<PolyFnSig>,
        generic_args: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<(Binder<FnOutput>, Obligations), CheckerErrKind> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(
            actuals,
            fn_sig
                .as_ref()
                .skip_binder()
                .as_ref()
                .skip_binder()
                .args(),
        )
        .map(|(actual, formal)| {
            if let (Ref!(.., Mutability::Mut), Ref!(_, ty, Mutability::Mut)) = (actual.kind(), formal.kind())
                && let TyKind::Indexed(..) = ty.kind()
            {
                rcx.unpacker().unpack_inside_mut_ref(true).unpack(actual)
            } else {
                actual.clone()
            }
        })
        .collect_vec();

        let genv = self.genv;
        let callsite_def_id = self.def_id;
        let span = self.span;

        let mut infcx = self.infcx(rcx, ConstrReason::Call);
        let snapshot = rcx.snapshot();

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        // Generate fresh inference variables for refinement arguments
        let refine_args = infcx.instantiate_refine_args(genv, callee_def_id)?;

        // Instantiate function signature and normalize it
        let inst_fn_sig = fn_sig
            .instantiate(&generic_args, &refine_args)
            .replace_bound_vars(
                |br| {
                    let re = infcx.region_infcx.next_region_var(LateBoundRegion(
                        span,
                        br.kind.to_rustc(),
                        LateBoundRegionConversionTime::FnCall,
                    ));
                    rty::ReVar(re.as_var())
                },
                |sort, mode| infcx.fresh_infer_var(sort, mode),
            )
            .normalize_projections(genv, infcx.region_infcx, callsite_def_id, infcx.refparams)?;

        let obligs = if let Some(did) = callee_def_id {
            mk_obligations(genv, did, &generic_args, &refine_args)?
        } else {
            List::empty()
        };

        // Check requires predicates and collect type constraints
        let mut requires = FxHashMap::default();
        for constr in inst_fn_sig.requires() {
            match constr {
                Constraint::Type(path, ty) => {
                    requires.insert(path.clone(), ty);
                }
                Constraint::Pred(pred) => {
                    infcx.check_pred(rcx, pred);
                }
            }
        }

        // Check arguments
        for (actual, formal) in iter::zip(&actuals, inst_fn_sig.args()) {
            let rcx = &mut rcx.push_comment(format!("{actual:?} <: {formal:?}"));

            let (formal, pred) = formal.unconstr();
            infcx.check_pred(rcx, pred);
            // TODO(pack-closure): Generalize/refactor to reuse for mutable closures
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path1), TyKind::Ptr(PtrKind::Mut(_), path2)) => {
                    let bound = requires[path2];
                    infcx.unify_exprs(&path1.to_expr(), &path2.to_expr(), false);
                    infcx.check_type_constr(rcx, env, path1, bound)?;
                }
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env.block_with(path, bound.clone());
                    infcx.subtyping(rcx, &ty, bound)?;
                }
                _ => infcx.subtyping(rcx, actual, &formal)?,
            }
        }

        // check (non-closure) obligations -- the closure ones are handled in `checker` since
        // as we have to recursively walk over their def_id bodies.
        for pred in &obligs {
            if let rty::ClauseKind::Projection(projection_pred) = pred.kind() {
                let impl_elem = Ty::projection(projection_pred.projection_ty)
                    .normalize_projections(
                        infcx.genv,
                        infcx.region_infcx,
                        callsite_def_id,
                        infcx.refparams,
                    )?;

                // TODO: does this really need to be invariant? https://github.com/flux-rs/flux/pull/478#issuecomment-1654035374
                infcx.subtyping(rcx, &impl_elem, &projection_pred.term)?;
                infcx.subtyping(rcx, &projection_pred.term, &impl_elem)?;
            }
        }
        // Replace evars
        let evars_sol = infcx.solve()?;
        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);
        let output = inst_fn_sig.output().replace_evars(&evars_sol);

        Ok((output, Obligations::new(obligs, snapshot)))
    }

    pub(crate) fn check_ret(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        output: &Binder<FnOutput>,
    ) -> Result<Obligations, CheckerErrKind> {
        let ret_place_ty = env.lookup_place(self.genv, rcx, Place::RETURN)?;

        let output = output.normalize_projections(
            self.genv,
            self.region_infcx,
            self.def_id,
            self.refparams,
        )?;

        let mut infcx = self.infcx(rcx, ConstrReason::Ret);

        let output =
            output.replace_bound_exprs_with(|sort, mode| infcx.fresh_infer_var(sort, mode));

        infcx.subtyping(rcx, &ret_place_ty, &output.ret)?;
        for constraint in &output.ensures {
            infcx.check_constraint(rcx, env, constraint)?;
        }

        let obligs = infcx.obligations();

        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(Obligations::new(obligs.into(), rcx.snapshot()))
    }

    pub(crate) fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: EarlyBinder<PolyVariant>,
        generic_args: &[GenericArg],
        fields: &[Ty],
    ) -> Result<Ty, CheckerErrKind> {
        // rn we are only calling `check_constructor` when folding so we mark this as a folding error.
        let mut infcx = self.infcx(rcx, ConstrReason::Fold);

        // Replace holes in generic arguments with fresh inference variables
        let generic_args = infcx.instantiate_generic_args(generic_args);

        let variant = variant
            .instantiate(&generic_args, &[])
            .replace_bound_exprs_with(|sort, mode| infcx.fresh_infer_var(sort, mode));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            infcx.subtyping(rcx, actual, formal)?;
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret.replace_evars(&evars_sol))
    }

    pub(crate) fn check_mk_array(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        args: &[Ty],
        arr_ty: Ty,
    ) -> Result<Ty, CheckerErrKind> {
        let mut infcx = self.infcx(rcx, ConstrReason::Other);

        let arr_ty =
            arr_ty.replace_holes(|binders, kind| infcx.fresh_infer_var_for_hole(binders, kind));

        let (arr_ty, pred) = arr_ty.unconstr();
        infcx.check_pred(rcx, pred);

        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut(_), path), Ref!(_, bound, Mutability::Mut)) => {
                    let ty = env.block_with(path, bound.clone());
                    infcx.subtyping(rcx, &ty, bound)?;
                }
                _ => infcx.subtyping(rcx, ty, &arr_ty)?,
            }
        }
        rcx.replace_evars(&infcx.solve()?);

        Ok(Ty::array(arr_ty, Const::from(args.len())))
    }

    pub(crate) fn infcx(&mut self, rcx: &RefineCtxt, reason: ConstrReason) -> InferCtxt<'_, 'tcx> {
        InferCtxt::new(
            self.genv,
            self.region_infcx,
            self.def_id,
            self.refparams,
            rcx,
            &mut self.kvar_gen,
            Tag::new(reason, self.span),
        )
    }
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        region_infcx: &'a rustc_infer::infer::InferCtxt<'tcx>,
        def_id: DefId,
        refparams: &'a [Expr],
        rcx: &RefineCtxt,
        kvar_gen: &'a mut (dyn KVarGen + 'a),
        tag: Tag,
    ) -> Self {
        let mut evar_gen = EVarGen::new();
        let mut scopes = FxIndexMap::default();
        scopes.insert(evar_gen.new_ctxt(), rcx.scope());
        Self {
            genv,
            region_infcx,
            def_id,
            refparams,
            kvar_gen,
            evar_gen,
            tag,
            scopes,
            obligs: Vec::new(),
        }
    }

    fn obligations(&self) -> Vec<rty::Clause> {
        self.obligs.clone()
    }

    fn insert_obligations(&mut self, obligs: Vec<rty::Clause>) {
        self.obligs.extend(obligs);
    }

    fn push_scope(&mut self, rcx: &RefineCtxt) {
        self.scopes.insert(self.evar_gen.new_ctxt(), rcx.scope());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn instantiate_refine_args(
        &mut self,
        genv: &GlobalEnv,
        callee_def_id: Option<DefId>,
    ) -> Result<Vec<Expr>, CheckerErrKind> {
        if let Some(callee_id) = callee_def_id {
            Ok(genv
                .generics_of(callee_id)?
                .collect_all_refine_params(genv, |param| {
                    self.fresh_infer_var(&param.sort, param.mode)
                })?)
        } else {
            Ok(vec![])
        }
    }

    fn instantiate_generic_args(&mut self, args: &[GenericArg]) -> Vec<GenericArg> {
        args.iter()
            .map(|a| a.replace_holes(|binders, kind| self.fresh_infer_var_for_hole(binders, kind)))
            .collect_vec()
    }

    pub(crate) fn fresh_infer_var(&mut self, sort: &Sort, mode: InferMode) -> Expr {
        match mode {
            InferMode::KVar => {
                let fsort = sort.expect_func().skip_binders();
                let inputs = List::from_slice(fsort.inputs());
                let kvar = self.fresh_kvar(&[inputs.clone()], KVarEncoding::Single);
                Expr::abs(Binder::with_sorts(kvar, inputs.iter().cloned()))
            }
            InferMode::EVar => self.fresh_evars(sort),
        }
    }

    fn fresh_infer_var_for_hole(&mut self, binders: &[List<Sort>], kind: HoleKind) -> Expr {
        match kind {
            HoleKind::Pred => self.fresh_kvar(binders, KVarEncoding::Conj),
            HoleKind::Expr(sort) => {
                assert!(binders.is_empty(), "TODO: implement evars under binders");
                self.fresh_evars(&sort)
            }
        }
    }

    pub(crate) fn fresh_kvar(&mut self, sorts: &[List<Sort>], encoding: KVarEncoding) -> Expr {
        self.kvar_gen.fresh(sorts, encoding)
    }

    fn fresh_evars(&mut self, sort: &Sort) -> Expr {
        let cx = *self.scopes.last().unwrap().0;
        Expr::fold_sort(sort, |_| Expr::evar(self.evar_gen.fresh_in_cx(cx)))
    }

    pub(crate) fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>) {
        rcx.check_pred(pred, self.tag);
    }

    fn check_type_constr(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        path: &Path,
        ty: &Ty,
    ) -> Result<(), CheckerErrKind> {
        let actual_ty = env.get(path);
        self.subtyping(rcx, &actual_ty, ty)
    }

    fn check_constraint(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        constraint: &Constraint,
    ) -> Result<(), CheckerErrKind> {
        let rcx = &mut rcx.branch();
        match constraint {
            Constraint::Type(path, ty) => self.check_type_constr(rcx, env, path, ty),
            Constraint::Pred(e) => {
                rcx.check_pred(e, self.tag);
                Ok(())
            }
        }
    }

    pub(crate) fn subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty1: &Ty,
        ty2: &Ty,
    ) -> Result<(), CheckerErrKind> {
        let rcx = &mut rcx.branch();

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(ty1), _) => {
                let ty1 = ty1.replace_bound_exprs_with(|sort, _| rcx.define_vars(sort));
                self.subtyping(rcx, &ty1, ty2)
            }
            (TyKind::Constr(p1, ty1), _) => {
                rcx.assume_pred(p1);
                self.subtyping(rcx, ty1, ty2)
            }
            (_, TyKind::Exists(ty2)) => {
                self.push_scope(rcx);
                let ty2 =
                    ty2.replace_bound_exprs_with(|sort, mode| self.fresh_infer_var(sort, mode));
                self.subtyping(rcx, ty1, &ty2)?;
                self.pop_scope();
                Ok(())
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.bty_subtyping(rcx, bty1, bty2)?;
                self.idx_subtyping(rcx, &idx1.expr, &idx2.expr, &idx2.is_binder);
                Ok(())
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
                Ok(())
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ok(())
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
                Ok(())
            }
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2, self.tag);
                self.subtyping(rcx, ty1, ty2)
            }
            (TyKind::Downcast(.., fields1), TyKind::Downcast(.., fields2)) => {
                debug_assert_eq!(fields1.len(), fields2.len());
                for (field1, field2) in iter::zip(fields1, fields2) {
                    self.subtyping(rcx, field1, field2)?;
                }
                Ok(())
            }
            (_, TyKind::Alias(rty::AliasKind::Opaque, alias_ty)) => {
                if let TyKind::Alias(rty::AliasKind::Opaque, alias_ty1) = ty1.kind() {
                    debug_assert_eq!(alias_ty1.refine_args.len(), alias_ty.refine_args.len());
                    iter::zip(alias_ty1.refine_args.iter(), alias_ty.refine_args.iter())
                        .for_each(|(e1, e2)| self.unify_exprs(e1, e2, false));
                }

                self.opaque_subtyping(rcx, ty1, alias_ty)
            }
            _ => tracked_span_bug!("`{ty1:?}` <: `{ty2:?}`"),
        }
    }

    fn bty_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        bty1: &BaseTy,
        bty2: &BaseTy,
    ) -> Result<(), CheckerErrKind> {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                Ok(())
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                Ok(())
            }
            (BaseTy::Adt(adt1, args1), BaseTy::Adt(adt2, args2)) => {
                debug_assert_eq!(adt1.did(), adt2.did());
                debug_assert_eq!(args1.len(), args2.len());
                let variances = self.genv.variances_of(adt1.did());
                for (variance, ty1, ty2) in izip!(variances, args1.iter(), args2.iter()) {
                    self.generic_arg_subtyping(rcx, *variance, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ok(())
            }

            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => self.subtyping(rcx, ty1, ty2),
            (BaseTy::Ref(_, ty1, Mutability::Mut), BaseTy::Ref(_, ty2, Mutability::Mut)) => {
                self.subtyping(rcx, ty1, ty2)?;
                self.subtyping(rcx, ty2, ty1)
            }
            (BaseTy::Ref(_, ty1, Mutability::Not), BaseTy::Ref(_, ty2, Mutability::Not)) => {
                self.subtyping(rcx, ty1, ty2)
            }
            (BaseTy::Tuple(tys1), BaseTy::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1, len2);
                self.subtyping(rcx, ty1, ty2)
            }
            (BaseTy::Param(param1), BaseTy::Param(param2)) => {
                debug_assert_eq!(param1, param2);
                Ok(())
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtr(_, _), BaseTy::RawPtr(_, _)) => Ok(()),
            (BaseTy::Closure(did1, tys1), BaseTy::Closure(did2, tys2)) if did1 == did2 => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2)?;
                }
                Ok(())
            }
            _ => {
                panic!("unexpected base types: `{:?}` and `{:?}`", bty1, bty2,);
            }
        }
    }

    fn project_bty(&mut self, self_ty: &Ty, def_id: DefId) -> Result<Ty, CheckerErrKind> {
        let args = vec![GenericArg::Ty(self_ty.clone())];
        let alias_ty = rty::AliasTy::new(def_id, args, List::empty());
        Ok(Ty::projection(alias_ty).normalize_projections(
            self.genv,
            self.region_infcx,
            self.def_id,
            self.refparams,
        )?)
    }

    fn opaque_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty: &Ty,
        alias_ty: &AliasTy,
    ) -> Result<(), CheckerErrKind> {
        if let Some(BaseTy::Generator(def_id, args)) = ty.as_bty_skipping_existentials() {
            let obligs = mk_generator_obligations(self.genv, def_id, args, &alias_ty.def_id)?;
            self.insert_obligations(obligs);
        } else {
            let bounds = self
                .genv
                .item_bounds(alias_ty.def_id)?
                .instantiate_identity(self.refparams);
            for clause in &bounds {
                if let rty::ClauseKind::Projection(pred) = clause.kind() {
                    let ty1 = self.project_bty(ty, pred.projection_ty.def_id)?;
                    let ty2 = pred.term;
                    self.subtyping(rcx, &ty1, &ty2)?;
                }
            }
        }
        Ok(())
    }

    fn generic_arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        variance: Variance,
        arg1: &GenericArg,
        arg2: &GenericArg,
    ) -> Result<(), CheckerErrKind> {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => {
                match variance {
                    Variance::Covariant => self.subtyping(rcx, ty1, ty2),
                    Variance::Invariant => {
                        self.subtyping(rcx, ty1, ty2)?;
                        self.subtyping(rcx, ty2, ty1)
                    }
                    Variance::Contravariant => self.subtyping(rcx, ty2, ty1),
                    Variance::Bivariant => Ok(()),
                }
            }
            (GenericArg::BaseTy(_), GenericArg::BaseTy(_)) => {
                tracked_span_bug!("sgeneric argument subtyping for base types is not implemented");
            }
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => Ok(()),
            _ => tracked_span_bug!("incompatible generic args: `{arg1:?}` `{arg2:?}"),
        }
    }

    fn idx_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        e1: &Expr,
        e2: &Expr,
        is_binder: &TupleTree<bool>,
    ) {
        if e1 == e2 {
            return;
        }

        match (e1.kind(), e2.kind()) {
            (ExprKind::Tuple(tup1), ExprKind::Tuple(tup2)) => {
                debug_assert_eq!(tup1.len(), tup2.len());

                for (e1, e2, is_binder) in izip!(tup1, tup2, is_binder.split()) {
                    self.idx_subtyping(rcx, e1, e2, is_binder);
                }
            }
            (ExprKind::Abs(p1), ExprKind::Abs(p2)) => {
                self.pred_subtyping(rcx, p1, p2);
            }
            (_, ExprKind::Abs(p)) => {
                self.pred_subtyping(rcx, &e1.eta_expand_abs(&p.vars().to_sort_list()), p);
            }
            (ExprKind::Abs(p), _) => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                self.pred_subtyping(rcx, p, &e2.eta_expand_abs(&p.vars().to_sort_list()));
            }
            _ => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                let span = e2.span();
                rcx.check_pred(Expr::binary_op(BinOp::Eq, e1, e2, span), self.tag);
            }
        }
    }

    fn pred_subtyping(&mut self, rcx: &mut RefineCtxt, p1: &Binder<Expr>, p2: &Binder<Expr>) {
        debug_assert_eq!(p1.vars(), p2.vars());
        let vars = p1
            .vars()
            .to_sort_list()
            .iter()
            .map(|s| rcx.define_vars(s))
            .collect_vec();
        let p1 = p1.replace_bound_exprs(&vars);
        let p2 = p2.replace_bound_exprs(&vars);
        rcx.check_impl(&p1, &p2, self.tag);
        rcx.check_impl(&p2, &p1, self.tag);
    }

    fn unify_exprs(&mut self, e1: &Expr, e2: &Expr, replace: bool) {
        if let ExprKind::Var(Var::EVar(evar)) = e2.kind()
           && let scope = &self.scopes[&evar.cx()]
           && !scope.has_free_vars(e1)
        {
            self.evar_gen.unify(*evar, e1, replace);
        }
    }

    pub(crate) fn solve(self) -> Result<EVarSol, UnsolvedEvar> {
        self.evar_gen.solve()
    }
}

impl Obligations {
    fn new(predicates: List<rty::Clause>, snapshot: Snapshot) -> Self {
        Self { predicates, snapshot }
    }
}

fn mk_generator_obligations(
    genv: &GlobalEnv<'_, '_>,
    generator_did: &DefId,
    generator_args: &GenericArgs,
    opaque_def_id: &DefId,
) -> Result<Vec<rty::Clause>, CheckerErrKind> {
    let bounds = genv.item_bounds(*opaque_def_id)?;
    let pred = if let rty::ClauseKind::Projection(proj) = bounds.skip_binder()[0].kind() {
        let output = proj.term;
        GeneratorObligPredicate { def_id: *generator_did, args: generator_args.clone(), output }
    } else {
        panic!("mk_generator_obligations: unexpected bounds")
    };
    let clause = rty::Clause::new(vec![], rty::ClauseKind::GeneratorOblig(pred));
    Ok(vec![clause])
}

fn mk_obligations(
    genv: &GlobalEnv<'_, '_>,
    did: DefId,
    args: &[GenericArg],
    refine_args: &[Expr],
) -> Result<List<rty::Clause>, CheckerErrKind> {
    Ok(genv
        .predicates_of(did)?
        .predicates()
        .instantiate(args, refine_args))
}

impl<F> KVarGen for F
where
    F: FnMut(&[List<Sort>], KVarEncoding) -> Expr,
{
    fn fresh(&mut self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr {
        (self)(binders, kind)
    }
}

impl<'a> KVarGen for &mut (dyn KVarGen + 'a) {
    fn fresh(&mut self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr {
        (**self).fresh(binders, kind)
    }
}

impl<'a> KVarGen for Box<dyn KVarGen + 'a> {
    fn fresh(&mut self, binders: &[List<Sort>], kind: KVarEncoding) -> Expr {
        (**self).fresh(binders, kind)
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;

    use super::*;

    impl Pretty for Tag {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} at {:?}", ^self.reason, self.src_span)
        }
    }

    impl_debug_with_default_cx!(Tag);
}
