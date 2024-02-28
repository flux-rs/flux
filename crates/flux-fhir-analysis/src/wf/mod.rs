//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod param_usage;
mod sortck;

use std::iter;

use flux_common::{
    result::{ErrorCollector, ResultExt as _},
    span_bug,
};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{self, visit::Visitor, FluxOwnerId, SurfaceIdent},
    global_env::GlobalEnv,
    rty::{self, WfckResults},
};
use rustc_data_structures::unord::UnordSet;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_span::Symbol;

use self::sortck::InferCtxt;
use crate::conv::{self, bug_on_infer_sort};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn check_item<'genv>(
    genv: GlobalEnv<'genv, '_>,
    item: &fhir::Item,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, item.owner_id.into());

    Wf::run(genv, |wf| {
        match &item.kind {
            fhir::ItemKind::Enum(enum_def) => {
                wf.check_enum_def(&mut infcx, enum_def);
            }
            fhir::ItemKind::Struct(struct_def) => {
                wf.check_struct_def(&mut infcx, struct_def);
            }
            fhir::ItemKind::TyAlias(ty_alias) => {
                wf.check_ty_alias(&mut infcx, ty_alias);
            }
            fhir::ItemKind::Trait(_) => {
                // TODO(nilehmann) we should check the sorts of associated predicates are well-formed.
            }
            fhir::ItemKind::Impl(impl_) => {
                wf.check_impl(&mut infcx, impl_);
            }
            fhir::ItemKind::Fn(fn_sig) => {
                wf.check_fn_decl(&mut infcx, fn_sig.decl);
            }
            fhir::ItemKind::OpaqueTy(opaque_ty) => {
                let parent = genv.tcx().local_parent(item.owner_id.def_id);
                if let Some(generics) = genv.map().get_generics(parent) {
                    let Some(wfckresults) = genv.check_wf(parent).emit(&wf.errors).ok() else {
                        return;
                    };
                    for param in generics.refinement_params {
                        let sort = wfckresults.node_sorts().get(param.fhir_id).unwrap().clone();
                        infcx.insert_param(param.id, sort, param.kind);
                    }
                }
                wf.check_opaque_ty(&mut infcx, opaque_ty);
            }
        }
    })?;

    ParamSortResolver::run(&mut infcx, |r| r.visit_item(item))?;

    param_usage::check_item(&infcx, item)?;

    Ok(infcx.into_results())
}

pub(crate) fn check_trait_item<'genv>(
    genv: GlobalEnv<'genv, '_>,
    trait_item: &fhir::TraitItem,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, trait_item.owner_id.into());
    Wf::run(genv, |wf| {
        match &trait_item.kind {
            fhir::TraitItemKind::Fn(fn_sig) => {
                wf.check_fn_decl(&mut infcx, fn_sig.decl);
            }
            fhir::TraitItemKind::Type(_) => {}
        }
    })?;
    ParamSortResolver::run(&mut infcx, |r| r.visit_trait_item(trait_item))?;

    param_usage::check_trait_item(&infcx, trait_item)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_impl_item<'genv>(
    genv: GlobalEnv<'genv, '_>,
    impl_item: &fhir::ImplItem,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, impl_item.owner_id.into());
    Wf::run(genv, |wf| {
        match &impl_item.kind {
            fhir::ImplItemKind::Fn(fn_sig) => {
                wf.check_fn_decl(&mut infcx, fn_sig.decl);
            }
            fhir::ImplItemKind::Type(_) => {}
        }
    })?;
    ParamSortResolver::run(&mut infcx, |r| r.visit_impl_item(impl_item))?;

    param_usage::check_impl_item(&infcx, impl_item)?;
    Ok(infcx.into_results())
}

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

struct Wf<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'genv, 'tcx> Wf<'genv, 'tcx> {
    fn run(genv: GlobalEnv<'genv, 'tcx>, f: impl FnOnce(&mut Wf)) -> Result {
        let mut wf = Wf { genv, errors: Errors::new(genv.sess()) };
        f(&mut wf);
        wf.errors.into_result()
    }

    fn check_generic_predicates(
        &mut self,
        infcx: &mut InferCtxt,
        predicates: &[fhir::WhereBoundPredicate],
    ) {
        for predicate in predicates {
            self.check_generic_predicate(infcx, predicate);
        }
    }

    fn check_generic_bound(&mut self, infcx: &mut InferCtxt, bound: &fhir::GenericBound) {
        match bound {
            fhir::GenericBound::Trait(trait_ref, _) => self.check_path(infcx, &trait_ref.trait_ref),
            fhir::GenericBound::LangItemTrait(_, args, bindings) => {
                self.check_generic_args(infcx, args);
                self.check_type_bindings(infcx, bindings);
            }
        }
    }

    fn check_opaque_ty(&mut self, infcx: &mut InferCtxt, opaque_ty: &fhir::OpaqueTy) {
        for bound in opaque_ty.bounds {
            self.check_generic_bound(infcx, bound);
        }
    }

    fn check_impl(&mut self, infcx: &mut InferCtxt, impl_: &fhir::Impl) {
        for assoc_reft in impl_.assoc_refinements {
            infcx.insert_params(assoc_reft.params);
            let output = conv::conv_sort(self.genv, &assoc_reft.output, &mut bug_on_infer_sort);
            infcx
                .check_expr(&assoc_reft.body, &output)
                .collect_err(&mut self.errors);
        }
    }

    fn check_ty_alias(&mut self, infcx: &mut InferCtxt, ty_alias: &fhir::TyAlias) {
        infcx.insert_params(ty_alias.generics.refinement_params);
        infcx.insert_params(ty_alias.index_params);
        self.check_type(infcx, &ty_alias.ty);
    }

    fn check_struct_def(&mut self, infcx: &mut InferCtxt, struct_def: &fhir::StructDef) {
        infcx.insert_params(struct_def.params);
        for invariant in struct_def.invariants {
            infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }

        if let fhir::StructKind::Transparent { fields } = struct_def.kind {
            for field_def in fields {
                self.check_type(infcx, &field_def.ty);
            }
        }
    }

    fn check_enum_def(&mut self, infcx: &mut InferCtxt, enum_def: &fhir::EnumDef) {
        infcx.insert_params(enum_def.params);
        for invariant in enum_def.invariants {
            infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }

        for variant in enum_def.variants {
            self.check_variant(infcx, variant);
        }
    }

    fn check_variant(&mut self, infcx: &mut InferCtxt, variant: &fhir::VariantDef) {
        infcx.insert_params(variant.params);

        let mut err: Option<ErrorGuaranteed> = None;
        for field in variant.fields {
            infcx.infer_implicit_params(&field.ty).collect_err(&mut err);
        }
        // Bail out if inference of implicit parameters failed to avoid confusing errors
        if let Some(err) = err {
            self.errors.collect_err(err);
            return;
        }

        for field in variant.fields {
            self.check_type(infcx, &field.ty);
        }

        let expected = {
            let bty = &variant.ret.bty;
            self.genv.sort_of_bty(bty).unwrap_or_else(|| {
                span_bug!(variant.ret.bty.span, "unrefinable base type: `{bty:?}`")
            })
        };

        infcx
            .check_refine_arg(&variant.ret.idx, &expected)
            .collect_err(&mut self.errors);
    }

    fn check_fn_decl(&mut self, infcx: &mut InferCtxt, decl: &fhir::FnDecl) {
        infcx.insert_params(decl.generics.refinement_params);

        let mut err = None;
        for arg in decl.args {
            infcx.infer_implicit_params(arg).collect_err(&mut err);
        }
        for constr in decl.requires {
            if let fhir::Constraint::Type(_, ty) = constr {
                infcx.infer_implicit_params(ty).collect_err(&mut err);
            }
        }

        // Bail out if inference of implicit parameters failed to avoid confusing errors
        if let Some(err) = err {
            self.errors.collect_err(err);
            return;
        }

        for arg in decl.args {
            self.check_type(infcx, arg);
        }

        for constr in decl.requires {
            self.check_constraint(infcx, constr);
        }

        self.check_generic_predicates(infcx, decl.generics.predicates);
        self.check_fn_output(infcx, &decl.output);
        self.check_output_locs(decl);
    }

    fn check_fn_output(&mut self, infcx: &mut InferCtxt, fn_output: &fhir::FnOutput) {
        infcx.insert_params(fn_output.params);
        infcx
            .infer_implicit_params(&fn_output.ret)
            .collect_err(&mut self.errors);

        self.check_type(infcx, &fn_output.ret);
        for constr in fn_output.ensures {
            self.check_constraint(infcx, constr);
        }
    }

    fn check_output_locs(&mut self, fn_decl: &fhir::FnDecl) {
        let mut output_locs = FxHashSet::default();
        for constr in fn_decl.output.ensures {
            if let fhir::Constraint::Type(loc, ..) = constr
                && let (_, id) = loc.res.expect_param()
                && !output_locs.insert(id)
            {
                self.errors.emit(errors::DuplicatedEnsures::new(loc));
            }
        }

        for constr in fn_decl.requires {
            if let fhir::Constraint::Type(loc, ..) = constr
                && let (_, id) = loc.res.expect_param()
                && !output_locs.contains(&id)
            {
                self.errors.emit(errors::MissingEnsures::new(loc));
            }
        }
    }

    fn check_constraint(&mut self, infcx: &mut InferCtxt, constr: &fhir::Constraint) {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                infcx.check_loc(loc).collect_err(&mut self.errors);
                self.check_type(infcx, ty);
            }
            fhir::Constraint::Pred(pred) => {
                infcx
                    .check_expr(pred, &rty::Sort::Bool)
                    .collect_err(&mut self.errors);
            }
        }
    }

    fn check_type(&mut self, infcx: &mut InferCtxt, ty: &fhir::Ty) {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.check_base_ty(infcx, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                if let Some(expected) = self.genv.sort_of_bty(bty) {
                    infcx
                        .check_refine_arg(idx, &expected)
                        .collect_err(&mut self.errors);
                } else if idx.is_colon_param().is_none() {
                    self.errors
                        .emit(errors::RefinedUnrefinableType::new(bty.span));
                }
                self.check_base_ty(infcx, bty);
            }
            fhir::TyKind::Exists(params, ty) => {
                infcx.insert_params(params);
                self.check_type(infcx, ty);
            }
            fhir::TyKind::Ptr(_, loc) => {
                infcx.check_loc(loc).collect_err(&mut self.errors);
            }
            fhir::TyKind::Tuple(tys) => {
                for ty in *tys {
                    self.check_type(infcx, ty);
                }
            }
            fhir::TyKind::Ref(_, fhir::MutTy { ty, .. }) | fhir::TyKind::Array(ty, _) => {
                self.check_type(infcx, ty);
            }
            fhir::TyKind::Constr(pred, ty) => {
                self.check_type(infcx, ty);
                infcx
                    .check_expr(pred, &rty::Sort::Bool)
                    .collect_err(&mut self.errors);
            }
            fhir::TyKind::OpaqueDef(_item_id, args, _refine_args, _) => {
                // TODO sanity check the _refine_args (though they should never fail!) but we'd need their expected sorts
                self.check_generic_args(infcx, args);
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(infcx, ty),
            fhir::TyKind::Hole(_) | fhir::TyKind::Never => {}
        }
    }

    fn check_generic_predicate(
        &mut self,
        infcx: &mut InferCtxt,
        predicate: &fhir::WhereBoundPredicate,
    ) {
        self.check_type(infcx, &predicate.bounded_ty);
        for bound in predicate.bounds {
            self.check_generic_bound(infcx, bound);
        }
    }

    fn check_generic_args(&mut self, infcx: &mut InferCtxt, args: &[fhir::GenericArg]) {
        for arg in args {
            self.check_generic_arg(infcx, arg);
        }
    }

    fn check_generic_arg(&mut self, infcx: &mut InferCtxt, arg: &fhir::GenericArg) {
        if let fhir::GenericArg::Type(ty) = arg {
            self.check_type(infcx, ty);
        }
    }

    fn check_type_bindings(&mut self, infcx: &mut InferCtxt, bindings: &[fhir::TypeBinding]) {
        for binding in bindings {
            self.check_type(infcx, &binding.term);
        }
    }

    fn check_base_ty(&mut self, infcx: &mut InferCtxt, bty: &fhir::BaseTy) {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) => {
                if let Some(self_ty) = self_ty {
                    self.check_type(infcx, self_ty);
                }
                self.check_path(infcx, path);
            }
            fhir::BaseTyKind::Slice(ty) => self.check_type(infcx, ty),
        }
    }

    fn check_path(&mut self, infcx: &mut InferCtxt, path: &fhir::Path) {
        match path.res {
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let Some(generics) = self
                    .genv
                    .refinement_generics_of(def_id)
                    .emit(&self.errors)
                    .ok()
                else {
                    return;
                };

                if path.refine.len() != generics.params.len() {
                    self.errors.emit(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        generics.params.len(),
                        path.refine.len(),
                    ));
                }

                for (arg, param) in iter::zip(path.refine, &generics.params) {
                    infcx
                        .check_refine_arg(arg, &param.sort)
                        .collect_err(&mut self.errors);
                }
            }
            fhir::Res::SelfTyParam { .. }
            | fhir::Res::SelfTyAlias { .. }
            | fhir::Res::Def(..)
            | fhir::Res::PrimTy(..)
            | fhir::Res::Err => {}
        }

        // TODO(nilehmann) we should check all segments
        let last_segment = path.last_segment();
        if !last_segment.args.is_empty() {
            self.check_generic_args(infcx, last_segment.args);
        }
        self.check_type_bindings(infcx, last_segment.bindings);
    }
}

/// Check that all params with [`fhir::Sort::Infer`] have a sort inferred and save it in the
/// [`WfckResults`]
struct ParamSortResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Option<ErrorGuaranteed>,
}

impl<'a, 'genv, 'tcx> ParamSortResolver<'a, 'genv, 'tcx> {
    fn run(
        infcx: &'a mut InferCtxt<'genv, 'tcx>,
        f: impl FnOnce(&mut ParamSortResolver),
    ) -> Result {
        let mut resolver = Self { infcx, errors: None };
        f(&mut resolver);
        resolver.errors.into_result()
    }
}

impl fhir::visit::Visitor for ParamSortResolver<'_, '_, '_> {
    fn visit_refine_param(&mut self, param: &fhir::RefineParam) {
        self.infcx
            .resolve_param_sort(param)
            .collect_err(&mut self.errors);
    }
}
