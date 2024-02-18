//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod sortck;

use std::iter;

use flux_common::{iter::IterExt, span_bug};
use flux_errors::{FluxSession, ResultExt};
use flux_middle::{
    fhir::{self, ExprRes, FluxOwnerId, SurfaceIdent},
    global_env::GlobalEnv,
    rty::{self, WfckResults},
};
use rustc_data_structures::{
    snapshot_map::{self, SnapshotMap},
    unord::UnordSet,
};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::FxHashSet;
use rustc_hir::{def::DefKind, OwnerId};
use rustc_span::Symbol;

use self::sortck::InferCtxt;
use crate::conv::{self, bug_on_infer_sort};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

struct Wf<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    xi: XiCtxt,
}

/// Keeps track of all refinement parameters that are used as an index such that their value is fully
/// determined. The context is called Xi because in the paper [Focusing on Liquid Refinement Typing],
/// the well-formedness judgment uses an uppercase Xi (Ξ) for a context that is similar in purpose.
///
/// This is basically a set of [`fhir::ParamId`] implemented with a snapshot map such that elements
/// can be removed in batch when there's a change in polarity.
///
/// [Focusing on Liquid Refinement Typing]: https://arxiv.org/pdf/2209.13000.pdf
#[derive(Default)]
struct XiCtxt(SnapshotMap<fhir::ParamId, ()>);

pub(crate) fn check_qualifier<'genv>(
    genv: GlobalEnv<'genv, '_>,
    qualifier: &fhir::Qualifier,
) -> Result<WfckResults<'genv>> {
    let owner = FluxOwnerId::Flux(qualifier.name);
    let mut infcx = InferCtxt::new(genv, owner);
    infcx.insert_params(qualifier.args);

    infcx.check_expr(&qualifier.expr, &rty::Sort::Bool)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_spec_func<'genv>(
    genv: GlobalEnv<'genv, '_>,
    func: &fhir::SpecFunc,
) -> Result<WfckResults<'genv>> {
    let owner = FluxOwnerId::Flux(func.name);
    let mut infcx = InferCtxt::new(genv, owner);
    if let Some(body) = &func.body {
        infcx.insert_params(func.args);
        let output = conv::conv_sort(genv, &func.sort, &mut bug_on_infer_sort);
        infcx.check_expr(body, &output)?;
    }
    Ok(infcx.into_results())
}

pub(crate) fn check_fn_quals(
    sess: &FluxSession,
    qualifiers: &UnordSet<Symbol>,
    fn_quals: &[SurfaceIdent],
) -> Result {
    for qual in fn_quals {
        if !qualifiers.contains(&qual.name) {
            let span = qual.span;
            return Err(sess.emit_err(errors::UnknownQualifier::new(span)));
        }
    }
    Ok(())
}

pub(crate) fn check_ty_alias<'genv>(
    genv: GlobalEnv<'genv, '_>,
    ty_alias: &fhir::TyAlias,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, ty_alias.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(ty_alias.generics.refinement_params);
    infcx.insert_params(ty_alias.index_params);

    wf.check_type(&mut infcx, &ty_alias.ty)?;
    wf.check_params_are_determined(&infcx, ty_alias.index_params)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_struct_def<'genv>(
    genv: GlobalEnv<'genv, '_>,
    struct_def: &fhir::StructDef,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, struct_def.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(struct_def.params);

    struct_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &rty::Sort::Bool))?;

    if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
        fields
            .iter()
            .try_for_each_exhaust(|field_def| wf.check_type(&mut infcx, &field_def.ty))?;
        wf.check_params_are_determined(&infcx, struct_def.params)?;
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_enum_def<'genv>(
    genv: GlobalEnv<'genv, '_>,
    enum_def: &fhir::EnumDef,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, enum_def.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(enum_def.params);

    enum_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &rty::Sort::Bool))?;

    // We are reusing the same `InferCtxt` which may contain some variables from the enum params.
    // This is not a problem because parameters in the variants with the same name will overwrite them.
    enum_def
        .variants
        .iter()
        .try_for_each_exhaust(|variant| wf.check_variant(&mut infcx, variant))?;

    Ok(infcx.into_results())
}

pub(crate) fn check_opaque_ty<'genv>(
    genv: GlobalEnv<'genv, '_>,
    opaque_ty: &fhir::OpaqueTy,
    owner_id: OwnerId,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);
    let parent = genv.tcx().local_parent(owner_id.def_id);
    if let Some(generics) = genv.map().get_generics(parent) {
        let wfckresults = genv.check_wf(parent).emit(genv.sess())?;
        for param in generics.refinement_params {
            let sort = wfckresults.node_sorts().get(param.fhir_id).unwrap().clone();
            infcx.insert_param(param.id, sort, param.kind);
        }
    }
    wf.check_opaque_ty(&mut infcx, opaque_ty)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_impl<'genv>(
    genv: GlobalEnv<'genv, '_>,
    impl_: &fhir::Impl,
    owner_id: OwnerId,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());

    for assoc_reft in impl_.assoc_refinements {
        infcx.insert_params(assoc_reft.params);
        let output = conv::conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort);
        infcx.check_expr(&assoc_reft.body, &output)?;
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_fn_decl<'genv>(
    genv: GlobalEnv<'genv, '_>,
    decl: &fhir::FnDecl,
    owner_id: OwnerId,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);

    infcx.insert_params(decl.generics.refinement_params);

    for arg in decl.args {
        infcx.infer_implicit_params_ty(arg)?;
    }
    for constr in decl.requires {
        infcx.infer_implicit_params_constraint(constr)?;
    }

    let args = decl
        .args
        .iter()
        .try_for_each_exhaust(|ty| wf.check_type(&mut infcx, ty));

    let requires = decl
        .requires
        .iter()
        .try_for_each_exhaust(|constr| wf.check_constraint(&mut infcx, constr));

    wf.check_generic_predicates(&mut infcx, decl.generics.predicates)?;

    let output = wf.check_fn_output(&mut infcx, &decl.output);

    let constrs = wf.check_output_locs(decl);

    args?;
    output?;
    requires?;
    constrs?;

    infcx.resolve_params_sorts(decl.generics.refinement_params)?;
    wf.check_params_are_determined(&infcx, decl.generics.refinement_params)?;

    Ok(infcx.into_results())
}

impl<'genv, 'tcx> Wf<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>) -> Self {
        Wf { genv, xi: Default::default() }
    }

    fn check_params_are_determined(
        &mut self,
        infcx: &InferCtxt,
        params: &[fhir::RefineParam],
    ) -> Result {
        params.iter().try_for_each_exhaust(|param| {
            let determined = self.xi.remove(param.id);
            if infcx.infer_mode(param.id) == fhir::InferMode::EVar && !determined {
                return self.emit_err(errors::ParamNotDetermined::new(param.span, param.name));
            }
            Ok(())
        })
    }

    fn check_generic_predicates(
        &mut self,
        infcx: &mut InferCtxt,
        predicates: &[fhir::WhereBoundPredicate],
    ) -> Result {
        predicates
            .iter()
            .try_for_each_exhaust(|pred| self.check_generic_predicate(infcx, pred))
    }

    fn check_generic_bound(&mut self, infcx: &mut InferCtxt, bound: &fhir::GenericBound) -> Result {
        match bound {
            fhir::GenericBound::Trait(trait_ref, _) => self.check_path(infcx, &trait_ref.trait_ref),
            fhir::GenericBound::LangItemTrait(_, args, bindings) => {
                self.check_generic_args(infcx, args)?;
                self.check_type_bindings(infcx, bindings)?;
                Ok(())
            }
        }
    }

    fn check_opaque_ty(&mut self, infcx: &mut InferCtxt, opaque_ty: &fhir::OpaqueTy) -> Result {
        opaque_ty
            .bounds
            .iter()
            .try_for_each_exhaust(|bound| self.check_generic_bound(infcx, bound))
    }

    fn check_variant(&mut self, infcx: &mut InferCtxt, variant: &fhir::VariantDef) -> Result {
        infcx.insert_params(variant.params);
        for field in variant.fields {
            infcx.infer_implicit_params_ty(&field.ty)?;
        }

        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|field| self.check_type(infcx, &field.ty));
        let expected = self.sort_of_bty(&variant.ret.bty);
        let indices = self.check_refine_arg(infcx, &variant.ret.idx, &expected);

        fields?;
        indices?;

        infcx.resolve_params_sorts(variant.params)?;
        self.check_params_are_determined(infcx, variant.params)?;

        Ok(())
    }

    fn check_fn_output(&mut self, infcx: &mut InferCtxt, fn_output: &fhir::FnOutput) -> Result {
        let snapshot = self.xi.snapshot();
        infcx.insert_params(fn_output.params);
        infcx.infer_implicit_params_ty(&fn_output.ret)?;

        self.check_type(infcx, &fn_output.ret)?;
        fn_output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constraint(infcx, constr))?;

        let params = self.check_params_are_determined(infcx, fn_output.params);

        self.xi.rollback_to(snapshot);
        infcx.resolve_params_sorts(fn_output.params)?;

        params
    }

    fn check_output_locs(&self, fn_decl: &fhir::FnDecl) -> Result {
        let mut output_locs = FxHashSet::default();
        fn_decl
            .output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| {
                if let fhir::Constraint::Type(loc, ..) = constr
                    && let (_, id) = loc.res.expect_param()
                    && !output_locs.insert(id)
                {
                    self.emit_err(errors::DuplicatedEnsures::new(loc))
                } else {
                    Ok(())
                }
            })?;

        fn_decl.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, ..) = constr
                && let (_, id) = loc.res.expect_param()
                && !output_locs.contains(&id)
            {
                self.emit_err(errors::MissingEnsures::new(loc))
            } else {
                Ok(())
            }
        })
    }

    fn check_constraint(&mut self, infcx: &mut InferCtxt, constr: &fhir::Constraint) -> Result {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [infcx.check_loc(loc), self.check_type(infcx, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_expr_as_pred(infcx, pred),
        }
    }

    fn check_type(&mut self, infcx: &mut InferCtxt, ty: &fhir::Ty) -> Result {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.check_base_ty(infcx, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                if let Some(expected) = self.genv.sort_of_bty(bty) {
                    self.check_refine_arg(infcx, idx, &expected)?;
                } else if idx.is_colon_param().is_none() {
                    return self.emit_err(errors::RefinedUnrefinableType::new(bty.span));
                }
                self.check_base_ty(infcx, bty)
            }
            fhir::TyKind::Exists(params, ty) => {
                infcx.insert_params(params);
                self.check_type(infcx, ty)?;
                infcx.resolve_params_sorts(params)?;
                self.check_params_are_determined(infcx, params)
            }
            fhir::TyKind::Ptr(_, loc) => {
                let (_, id) = loc.res.expect_param();
                self.xi.insert(id);
                infcx.check_loc(loc)
            }
            fhir::TyKind::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(infcx, ty))
            }
            fhir::TyKind::Ref(_, fhir::MutTy { ty, .. }) | fhir::TyKind::Array(ty, _) => {
                self.check_type(infcx, ty)
            }
            fhir::TyKind::Constr(pred, ty) => {
                self.check_type(infcx, ty)?;
                self.check_expr_as_pred(infcx, pred)
            }
            fhir::TyKind::OpaqueDef(_item_id, args, _refine_args, _) => {
                // TODO sanity check the _refine_args (though they should never fail!) but we'd need their expected sorts
                self.check_generic_args(infcx, args)
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(infcx, ty),
            fhir::TyKind::Hole(_) | fhir::TyKind::Never => Ok(()),
        }
    }

    fn check_generic_predicate(
        &mut self,
        infcx: &mut InferCtxt,
        predicate: &fhir::WhereBoundPredicate,
    ) -> Result {
        self.check_type(infcx, &predicate.bounded_ty)?;
        predicate
            .bounds
            .iter()
            .map(|bound| self.check_generic_bound(infcx, bound))
            .try_collect_exhaust()
    }

    fn check_generic_args(&mut self, infcx: &mut InferCtxt, args: &[fhir::GenericArg]) -> Result {
        args.iter()
            .try_for_each_exhaust(|arg| self.check_generic_arg(infcx, arg))
    }

    fn check_generic_arg(&mut self, infcx: &mut InferCtxt, arg: &fhir::GenericArg) -> Result {
        if let fhir::GenericArg::Type(ty) = arg {
            self.check_type(infcx, ty)
        } else {
            Ok(())
        }
    }

    fn check_type_bindings(
        &mut self,
        infcx: &mut InferCtxt,
        bindings: &[fhir::TypeBinding],
    ) -> Result {
        bindings
            .iter()
            .try_for_each_exhaust(|binding| self.check_type(infcx, &binding.term))
    }

    fn check_base_ty(&mut self, infcx: &mut InferCtxt, bty: &fhir::BaseTy) -> Result {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) => {
                if let Some(self_ty) = self_ty {
                    self.check_type(infcx, self_ty)?;
                }
                self.check_path(infcx, path)
            }
            fhir::BaseTyKind::Slice(ty) => self.check_type(infcx, ty),
        }
    }

    fn check_path(&mut self, infcx: &mut InferCtxt, path: &fhir::Path) -> Result {
        match path.res {
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let generics = self
                    .genv
                    .refinement_generics_of(def_id)
                    .emit(self.genv.sess())?;

                if path.refine.len() != generics.params.len() {
                    return self.emit_err(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        generics.params.len(),
                        path.refine.len(),
                    ));
                }
                iter::zip(path.refine, &generics.params).try_for_each_exhaust(|(arg, param)| {
                    self.check_refine_arg(infcx, arg, &param.sort)
                })?;
            }
            fhir::Res::SelfTyParam { .. }
            | fhir::Res::SelfTyAlias { .. }
            | fhir::Res::Def(..)
            | fhir::Res::PrimTy(..) => {}
        }
        let snapshot = self.xi.snapshot();

        // TODO(nilehmann) we should check all segments
        let last_segment = path.last_segment();
        if !last_segment.args.is_empty() {
            self.check_generic_args(infcx, last_segment.args)?;
        }
        let bindings = self.check_type_bindings(infcx, last_segment.bindings);
        if !self.genv.is_box(path.res) {
            self.xi.rollback_to(snapshot);
        }
        bindings?;
        Ok(())
    }

    fn check_refine_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::RefineArg,
        expected: &rty::Sort,
    ) -> Result {
        infcx.check_refine_arg(arg, expected)?;
        self.check_param_uses_refine_arg(infcx, arg)
    }

    fn check_expr_as_pred(&mut self, infcx: &mut InferCtxt, expr: &fhir::Expr) -> Result {
        infcx.check_expr(expr, &rty::Sort::Bool)?;
        self.check_param_uses_expr(infcx, expr, true)
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_refine_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::RefineArg,
    ) -> Result {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => {
                if let fhir::ExprKind::Var(var, _) = &expr.kind {
                    if let ExprRes::Param(_, id) = var.res {
                        self.xi.insert(id);
                    }
                } else {
                    self.check_param_uses_expr(infcx, expr, false)?;
                }
                Ok(())
            }
            fhir::RefineArgKind::Abs(_, body) => self.check_param_uses_expr(infcx, body, true),
            fhir::RefineArgKind::Record(flds) => {
                flds.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_refine_arg(infcx, arg))
            }
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_expr(
        &self,
        infcx: &mut InferCtxt,
        expr: &fhir::Expr,
        is_top_level_conj: bool,
    ) -> Result {
        match expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, e1, e2) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                self.check_param_uses_expr(infcx, e1, is_pred)?;
                self.check_param_uses_expr(infcx, e2, is_pred)
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses_expr(infcx, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                    && let ExprRes::Param(_, id) = func.res
                    && let fhir::InferMode::KVar = infcx.infer_mode(id)
                {
                    return self
                        .emit_err(errors::InvalidParamPos::new(func.span, &infcx.param_sort(id)));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_expr(infcx, arg, false))
            }
            fhir::ExprKind::Alias(_, func_args) => {
                // TODO(nilehmann) should we check the usage inside the `AliasPred`?
                func_args
                    .iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_expr(infcx, arg, false))
            }
            fhir::ExprKind::Var(var, _) => {
                if let ExprRes::Param(_, id) = var.res
                    && let sort @ rty::Sort::Func(_) = infcx.param_sort(id)
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.span, &sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(e1, e2, e3) => {
                self.check_param_uses_expr(infcx, e1, false)?;
                self.check_param_uses_expr(infcx, e3, false)?;
                self.check_param_uses_expr(infcx, e2, false)
            }
            fhir::ExprKind::Literal(_) => Ok(()),
            fhir::ExprKind::Dot(var, _) => {
                if let ExprRes::Param(_, id) = var.res
                    && let sort @ rty::Sort::Func(_) = &infcx.param_sort(id)
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.span, sort));
                }
                Ok(())
            }
        }
    }

    fn sort_of_bty(&self, bty: &fhir::BaseTy) -> rty::Sort {
        self.genv
            .sort_of_bty(bty)
            .unwrap_or_else(|| span_bug!(bty.span, "unrefinable base type: `{bty:?}`"))
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R> {
        Err(self.genv.sess().emit_err(err))
    }
}

impl XiCtxt {
    fn insert(&mut self, id: fhir::ParamId) {
        self.0.insert(id, ());
    }

    fn remove(&mut self, id: fhir::ParamId) -> bool {
        self.0.remove(id)
    }

    fn snapshot(&mut self) -> snapshot_map::Snapshot {
        self.0.snapshot()
    }

    fn rollback_to(&mut self, snapshot: snapshot_map::Snapshot) {
        self.0.rollback_to(snapshot);
    }
}
