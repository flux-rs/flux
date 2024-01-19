//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod sortck;

use std::iter;

use flux_common::{bug, iter::IterExt, span_bug};
use flux_errors::{FluxSession, ResultExt};
use flux_middle::{
    fhir::{self, FluxOwnerId, SurfaceIdent},
    global_env::GlobalEnv,
    pretty::def_id_to_string,
    rty::{self, GenericParamDefKind, WfckResults},
};
use rustc_data_structures::snapshot_map::{self, SnapshotMap};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::FxHashSet;
use rustc_hir::{def::DefKind, def_id::DefId, OwnerId};
use rustc_span::{Span, Symbol};

use self::sortck::InferCtxt;
use crate::conv::{self, ConvCtxt};

struct Wf<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    xi: XiCtxt,
}

/// Keeps track of all refinement parameters that are used as an index such that their value is fully
/// determined. The context is called Xi because in the paper [Focusing on Liquid Refinement Typing],
/// the well-formedness judgment uses an uppercase Xi (Ξ) for a context that is similar in purpose.
///
/// This is basically a set of [`fhir::Name`] implemented with a snapshot map such that elements
/// can be removed in batch when there's a change in polarity.
///
/// [Focusing on Liquid Refinement Typing]: https://arxiv.org/pdf/2209.13000.pdf
#[derive(Default)]
struct XiCtxt(SnapshotMap<fhir::Name, ()>);

pub(crate) fn check_qualifier(
    genv: &GlobalEnv,
    qualifier: &fhir::Qualifier,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(qualifier.name);
    let mut infcx = InferCtxt::new(genv, owner);
    infcx.insert_params(&qualifier.args);

    infcx.check_expr(&qualifier.expr, &rty::Sort::Bool)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_defn(
    genv: &GlobalEnv,
    defn: &fhir::Defn,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(defn.name);
    let mut infcx = InferCtxt::new(genv, owner);
    infcx.insert_params(&defn.args);

    let output = conv::conv_sort(genv, &defn.sort, &mut || bug!("unexpected infer sort"));
    infcx.check_expr(&defn.expr, &output)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_fn_quals(
    sess: &FluxSession,
    qualifiers: &FxHashSet<Symbol>,
    fn_quals: &Vec<SurfaceIdent>,
) -> Result<(), ErrorGuaranteed> {
    for qual in fn_quals {
        if !qualifiers.contains(&qual.name) {
            let span = qual.span;
            return Err(sess.emit_err(errors::UnknownQualifier::new(span)));
        }
    }
    Ok(())
}

pub(crate) fn check_ty_alias(
    genv: &GlobalEnv,
    ty_alias: &fhir::TyAlias,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, ty_alias.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(&ty_alias.early_bound_params);
    infcx.insert_params(&ty_alias.index_params);

    wf.check_type(&mut infcx, &ty_alias.ty)?;
    wf.check_params_are_determined(&infcx, &ty_alias.index_params)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_struct_def(
    genv: &GlobalEnv,
    struct_def: &fhir::StructDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, struct_def.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(&struct_def.params);

    struct_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &rty::Sort::Bool))?;

    if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
        fields
            .iter()
            .try_for_each_exhaust(|field_def| wf.check_type(&mut infcx, &field_def.ty))?;
        wf.check_params_are_determined(&infcx, &struct_def.params)?;
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_enum_def(
    genv: &GlobalEnv,
    enum_def: &fhir::EnumDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, enum_def.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.insert_params(&enum_def.params);

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

pub(crate) fn check_opaque_ty(
    genv: &GlobalEnv,
    opaque_ty: &fhir::OpaqueTy,
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);
    let parent = genv.tcx.local_parent(owner_id.def_id);
    if let Some(params) = genv.map().get_refine_params(genv.tcx, parent) {
        let wfckresults = genv.check_wf(parent).emit(genv.sess)?;
        for param in params {
            let sort = wfckresults.node_sorts().get(param.fhir_id).unwrap().clone();
            infcx.insert_param(param.name(), sort, param.kind);
        }
    }
    wf.check_opaque_ty(&mut infcx, opaque_ty)?;
    Ok(infcx.into_results())
}

fn check_assoc_predicate_params(
    genv: &GlobalEnv,
    owner_id: OwnerId,
    name: Symbol,
    params: &[fhir::RefineParam],
    span: Span,
) -> Result<(), ErrorGuaranteed> {
    let impl_id = owner_id.def_id.to_def_id();
    let Some(sorts) = genv.sort_of_assoc_pred(impl_id, name).emit(genv.sess)? else {
        let trait_id = genv
            .tcx
            .impl_trait_ref(impl_id)
            .unwrap()
            .skip_binder()
            .def_id;
        let trait_id = def_id_to_string(trait_id);
        return Err(genv
            .sess
            .emit_err(errors::InvalidAssocPredicate::new(span, name, trait_id)));
    };

    {
        if sorts.len() != params.len() {
            return Err(genv.sess.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("associated predicate"),
                sorts.len(),
                params.len(),
            )));
        }
        for (param, sort) in iter::zip(params, &sorts) {
            let param_sort =
                conv::conv_sort(genv, &param.sort, &mut || bug!("unexpected infer sort"));
            if param_sort != *sort {
                return Err(genv.sess.emit_err(errors::SortMismatch::new(
                    param.span,
                    sort.clone(),
                    param_sort,
                )));
            }
        }
    }
    Ok(())
}

pub(crate) fn check_assoc_predicates(
    genv: &GlobalEnv,
    assoc_predicates: &[fhir::AssocPredicate],
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());

    // TODO(RJ): multiple-predicates

    for assoc_pred in assoc_predicates {
        if let fhir::AssocPredicateKind::Impl(params, body) = &assoc_pred.kind {
            // 1. Check this impl sorts conform to spec
            check_assoc_predicate_params(genv, owner_id, assoc_pred.name, params, assoc_pred.span)?;

            // 2. Check this impl is well-sorted
            infcx.insert_params(params);
            infcx.check_expr(body, &rty::Sort::Bool)?;
        }
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_fn_sig(
    genv: &GlobalEnv,
    fn_sig: &fhir::FnSig,
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);

    infcx.insert_params(&fn_sig.params);

    for arg in &fn_sig.args {
        infcx.infer_implicit_params_ty(arg)?;
    }
    for constr in &fn_sig.requires {
        infcx.infer_implicit_params_constraint(constr)?;
    }

    let args = fn_sig
        .args
        .iter()
        .try_for_each_exhaust(|ty| wf.check_type(&mut infcx, ty));

    let requires = fn_sig
        .requires
        .iter()
        .try_for_each_exhaust(|constr| wf.check_constraint(&mut infcx, constr));

    wf.check_generic_predicates(&mut infcx, &fn_sig.generics.predicates)?;

    let output = wf.check_fn_output(&mut infcx, &fn_sig.output);

    let constrs = wf.check_output_locs(fn_sig);

    args?;
    output?;
    requires?;
    constrs?;

    infcx.resolve_params_sorts(&fn_sig.params)?;
    wf.check_params_are_determined(&infcx, &fn_sig.params)?;

    Ok(infcx.into_results())
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>) -> Self {
        Wf { genv, xi: Default::default() }
    }

    fn check_params_are_determined(
        &mut self,
        infcx: &InferCtxt,
        params: &[fhir::RefineParam],
    ) -> Result<(), ErrorGuaranteed> {
        params.iter().try_for_each_exhaust(|param| {
            let determined = self.xi.remove(param.name());
            if infcx.infer_mode(param.ident) == fhir::InferMode::EVar && !determined {
                return self.emit_err(errors::ParamNotDetermined::new(param.ident));
            }
            Ok(())
        })
    }

    fn check_generic_predicates(
        &mut self,
        infcx: &mut InferCtxt,
        predicates: &[fhir::WhereBoundPredicate],
    ) -> Result<(), ErrorGuaranteed> {
        predicates
            .iter()
            .try_for_each_exhaust(|pred| self.check_generic_predicate(infcx, pred))
    }

    fn check_generic_bound(
        &mut self,
        infcx: &mut InferCtxt,
        bound: &fhir::GenericBound,
    ) -> Result<(), ErrorGuaranteed> {
        match bound {
            fhir::GenericBound::Trait(trait_ref, _) => self.check_path(infcx, &trait_ref.trait_ref),
            fhir::GenericBound::LangItemTrait(lang_item, args, bindings) => {
                let def_id = self.genv.tcx.require_lang_item(*lang_item, None);
                self.check_generic_args(infcx, def_id, args)?;
                self.check_type_bindings(infcx, bindings)?;
                Ok(())
            }
        }
    }

    fn check_opaque_ty(
        &mut self,
        infcx: &mut InferCtxt,
        opaque_ty: &fhir::OpaqueTy,
    ) -> Result<(), ErrorGuaranteed> {
        opaque_ty
            .bounds
            .iter()
            .try_for_each_exhaust(|bound| self.check_generic_bound(infcx, bound))
    }

    fn check_variant(
        &mut self,
        infcx: &mut InferCtxt,
        variant: &fhir::VariantDef,
    ) -> Result<(), ErrorGuaranteed> {
        infcx.insert_params(&variant.params);
        for field in &variant.fields {
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

        infcx.resolve_params_sorts(&variant.params)?;
        self.check_params_are_determined(infcx, &variant.params)?;

        Ok(())
    }

    fn check_fn_output(
        &mut self,
        infcx: &mut InferCtxt,
        fn_output: &fhir::FnOutput,
    ) -> Result<(), ErrorGuaranteed> {
        let snapshot = self.xi.snapshot();
        infcx.insert_params(&fn_output.params);
        infcx.infer_implicit_params_ty(&fn_output.ret)?;

        self.check_type(infcx, &fn_output.ret)?;
        fn_output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constraint(infcx, constr))?;

        let params = self.check_params_are_determined(infcx, &fn_output.params);

        self.xi.rollback_to(snapshot);
        infcx.resolve_params_sorts(&fn_output.params)?;

        params
    }

    fn check_output_locs(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut output_locs = FxHashSet::default();
        fn_sig
            .output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| {
                if let fhir::Constraint::Type(loc, ..) = constr
                    && !output_locs.insert(loc.name)
                {
                    self.emit_err(errors::DuplicatedEnsures::new(loc))
                } else {
                    Ok(())
                }
            })?;

        fn_sig.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, ..) = constr
                && !output_locs.contains(&loc.name)
            {
                self.emit_err(errors::MissingEnsures::new(loc))
            } else {
                Ok(())
            }
        })
    }

    fn check_constraint(
        &mut self,
        infcx: &mut InferCtxt,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty, _) => {
                [infcx.check_loc(*loc), self.check_type(infcx, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_expr_as_pred(infcx, pred),
        }
    }

    fn check_type(&mut self, infcx: &mut InferCtxt, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
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
                self.xi.insert(loc.name);
                infcx.check_loc(*loc)
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
                self.check_pred(infcx, pred)
            }
            fhir::TyKind::OpaqueDef(item_id, args, _refine_args, _) => {
                // TODO sanity check the _refine_args (though they should never fail!) but we'd need their expected sorts
                let def_id = item_id.owner_id.to_def_id();
                self.check_generic_args(infcx, def_id, args)
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(infcx, ty),
            fhir::TyKind::Hole(_) | fhir::TyKind::Never => Ok(()),
        }
    }

    fn check_generic_predicate(
        &mut self,
        infcx: &mut InferCtxt,
        predicate: &fhir::WhereBoundPredicate,
    ) -> Result<(), ErrorGuaranteed> {
        self.check_type(infcx, &predicate.bounded_ty)?;
        predicate
            .bounds
            .iter()
            .map(|bound| self.check_generic_bound(infcx, bound))
            .try_collect_exhaust()
    }

    fn check_ty_is_spl(&self, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) | fhir::TyKind::Indexed(bty, _) => {
                if self.genv.sort_of_bty(bty).is_none() {
                    return self.emit_err(errors::InvalidBaseInstance::new(ty));
                }
                Ok(())
            }
            fhir::TyKind::Tuple(tys) => {
                for ty in tys {
                    self.check_ty_is_spl(ty)?;
                }
                Ok(())
            }
            fhir::TyKind::Constr(_, ty) | fhir::TyKind::Exists(_, ty) => self.check_ty_is_spl(ty),

            fhir::TyKind::Ptr(_, _)
            | fhir::TyKind::Ref(_, _)
            | fhir::TyKind::Array(_, _)
            | fhir::TyKind::RawPtr(_, _)
            | fhir::TyKind::OpaqueDef(_, _, _, _)
            | fhir::TyKind::Never
            | fhir::TyKind::Hole(_) => self.emit_err(errors::InvalidBaseInstance::new(ty)),
        }
    }

    fn check_generic_args_kinds(
        &self,
        def_id: DefId,
        args: &[fhir::GenericArg],
    ) -> Result<(), ErrorGuaranteed> {
        let generics = self.genv.generics_of(def_id).emit(self.genv.sess)?;
        for (arg, param) in iter::zip(args, &generics.params) {
            if param.kind == GenericParamDefKind::SplTy {
                if let fhir::GenericArg::Type(ty) = arg {
                    self.check_ty_is_spl(ty)?;
                } else {
                    bug!("expected type argument got `{arg:?}`");
                }
            }
        }
        Ok(())
    }

    fn check_generic_args(
        &mut self,
        infcx: &mut InferCtxt,
        def_id: DefId,
        args: &[fhir::GenericArg],
    ) -> Result<(), ErrorGuaranteed> {
        self.check_generic_args_kinds(def_id, args)?;
        args.iter()
            .try_for_each_exhaust(|arg| self.check_generic_arg(infcx, arg))
    }

    fn check_generic_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::GenericArg,
    ) -> Result<(), ErrorGuaranteed> {
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
    ) -> Result<(), ErrorGuaranteed> {
        bindings
            .iter()
            .try_for_each_exhaust(|binding| self.check_type(infcx, &binding.term))
    }

    fn check_base_ty(
        &mut self,
        infcx: &mut InferCtxt,
        bty: &fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
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

    fn check_path(
        &mut self,
        infcx: &mut InferCtxt,
        path: &fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
        match &path.res {
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let generics = self
                    .genv
                    .refinement_generics_of(*def_id)
                    .emit(self.genv.sess)?;

                if path.refine.len() != generics.params.len() {
                    return self.emit_err(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        generics.params.len(),
                        path.refine.len(),
                    ));
                }
                iter::zip(&path.refine, &generics.params).try_for_each_exhaust(
                    |(arg, param)| self.check_refine_arg(infcx, arg, &param.sort),
                )?;
            }
            fhir::Res::SelfTyParam { .. }
            | fhir::Res::SelfTyAlias { .. }
            | fhir::Res::Def(..)
            | fhir::Res::PrimTy(..) => {}
        }
        let snapshot = self.xi.snapshot();

        if let fhir::Res::Def(_kind, did) = &path.res
            && !path.args.is_empty()
        {
            self.check_generic_args(infcx, *did, &path.args)?;
        }
        let bindings = self.check_type_bindings(infcx, &path.bindings);
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
    ) -> Result<(), ErrorGuaranteed> {
        infcx.check_refine_arg(arg, expected)?;
        self.check_param_uses_refine_arg(infcx, arg)
    }

    fn check_expr_as_pred(
        &mut self,
        infcx: &mut InferCtxt,
        expr: &fhir::Expr,
    ) -> Result<(), ErrorGuaranteed> {
        infcx.check_expr(expr, &rty::Sort::Bool)?;
        self.check_param_uses_expr(infcx, expr, true)
    }

    // A bit nasty that we have to `conv` the alias_pred.generic_args to use the [GenericsSubstFolder] in [sort_of_alias_pred]
    // I suppose its ok to use these empty `Env` as these generic_args are totally unrefined, but it would be nice to have that
    // explicitly enforced.
    fn check_alias_pred_app(
        &mut self,
        infcx: &mut InferCtxt,
        alias_pred: &fhir::AliasPred,
        args: &[fhir::RefineArg],
        span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let conv = ConvCtxt::new(self.genv, &infcx.wfckresults);
        let mut env = conv::Env::new(self.genv, &[], &infcx.wfckresults);
        let generic_args = conv
            .conv_generic_args(&mut env, alias_pred.trait_id, &alias_pred.generic_args)
            .emit(self.genv.sess)?;

        if let Some(inputs) = self
            .genv
            .sort_of_alias_pred(alias_pred, &generic_args)
            .emit(self.genv.sess)?
        {
            if args.len() != inputs.len() {
                return self.emit_err(errors::ArgCountMismatch::new(
                    Some(span),
                    String::from("function"),
                    inputs.len(),
                    args.len(),
                ));
            }
            iter::zip(args, &inputs)
                .try_for_each_exhaust(|(arg, formal)| self.check_refine_arg(infcx, arg, formal))?;
        }
        Ok(())
    }

    fn check_pred(
        &mut self,
        infcx: &mut InferCtxt,
        pred: &fhir::Pred,
    ) -> Result<(), ErrorGuaranteed> {
        match &pred.kind {
            fhir::PredKind::Expr(expr) => self.check_expr_as_pred(infcx, expr),
            fhir::PredKind::Alias(alias_pred, args) => {
                self.check_alias_pred_app(infcx, alias_pred, args, pred.span)
            }
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_refine_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::RefineArg,
    ) -> Result<(), ErrorGuaranteed> {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => {
                if let fhir::ExprKind::Var(var, _) = &expr.kind {
                    self.xi.insert(var.name);
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
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, exprs) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(infcx, e, is_pred))
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses_expr(infcx, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                    && let fhir::Func::Var(var, _) = func
                    && let fhir::InferMode::KVar = infcx.infer_mode(*var)
                {
                    return self.emit_err(errors::InvalidParamPos::new(
                        var.span(),
                        &infcx.lookup_var(*var),
                    ));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_expr(infcx, arg, false))
            }
            fhir::ExprKind::Var(var, _) => {
                if let sort @ rty::Sort::Func(_) = &infcx.lookup_var(*var) {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(exprs) => {
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(infcx, e, false))
            }
            fhir::ExprKind::Literal(_) | fhir::ExprKind::Const(_, _) => Ok(()),
            fhir::ExprKind::Dot(var, _) => {
                if let sort @ rty::Sort::Func(_) = &infcx.lookup_var(*var) {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
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
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.genv.sess.emit_err(err))
    }
}

impl XiCtxt {
    fn insert(&mut self, name: fhir::Name) {
        self.0.insert(name, ());
    }

    fn remove(&mut self, name: fhir::Name) -> bool {
        self.0.remove(name)
    }

    fn snapshot(&mut self) -> snapshot_map::Snapshot {
        self.0.snapshot()
    }

    fn rollback_to(&mut self, snapshot: snapshot_map::Snapshot) {
        self.0.rollback_to(snapshot);
    }
}
