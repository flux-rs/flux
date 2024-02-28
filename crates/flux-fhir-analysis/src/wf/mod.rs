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

use self::sortck::{ImplicitParamInferer, InferCtxt};
use crate::conv::{self, bug_on_infer_sort};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn check_node<'genv>(
    genv: GlobalEnv<'genv, '_>,
    node: &fhir::Node,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, node.owner_id().into());

    insert_params(&mut infcx, node)?;

    ImplicitParamInferer::infer(&mut infcx, node)?;

    SortCk::check_node(&mut infcx, node)?;

    resolve_params(&mut infcx, node)?;

    param_usage::check_node(&infcx, node)?;

    Ok(infcx.into_results())
}

/// Initializes the inference context with all parameters required to check node
fn insert_params(infcx: &mut InferCtxt, node: &fhir::Node) -> Result {
    if let fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::OpaqueTy(..), owner_id }) = node {
        let genv = infcx.genv;
        let parent = genv.tcx().local_parent(owner_id.def_id);
        if let Some(generics) = genv.map().get_generics(parent) {
            let wfckresults = genv.check_wf(parent).emit(genv.sess())?;
            for param in generics.refinement_params {
                let sort = wfckresults.node_sorts().get(param.fhir_id).unwrap().clone();
                infcx.insert_param(param.id, sort, param.kind);
            }
        }
    }
    visit_refine_params(node, |param| {
        let sort = conv::conv_sort(infcx.genv, &param.sort, &mut || infcx.next_sort_var());
        infcx.insert_param(param.id, sort, param.kind);
    });
    Ok(())
}

/// Check that all params with [`fhir::Sort::Infer`] have a sort inferred and save it in the [`WfckResults`]
fn resolve_params(infcx: &mut InferCtxt, node: &fhir::Node) -> Result {
    let mut err = None;
    visit_refine_params(node, |param| {
        infcx.resolve_param_sort(param).collect_err(&mut err);
    });
    err.into_result()
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

struct SortCk<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'genv, 'tcx> SortCk<'genv, 'tcx> {
    fn check_node(infcx: &mut InferCtxt<'genv, 'tcx>, node: &fhir::Node) -> Result {
        let mut wf = SortCk { genv: infcx.genv, errors: Errors::new(infcx.genv.sess()) };
        match node {
            fhir::Node::Item(item) => wf.check_item(infcx, item),
            fhir::Node::TraitItem(trait_item) => wf.check_trait_item(infcx, trait_item),
            fhir::Node::ImplItem(impl_item) => wf.check_impl_item(infcx, impl_item),
        }
        wf.errors.into_result()
    }

    fn check_item(&mut self, infcx: &mut InferCtxt, item: &fhir::Item) {
        match &item.kind {
            fhir::ItemKind::Enum(enum_def) => {
                self.check_enum_def(infcx, enum_def);
            }
            fhir::ItemKind::Struct(struct_def) => {
                self.check_struct_def(infcx, struct_def);
            }
            fhir::ItemKind::TyAlias(ty_alias) => {
                self.check_ty_alias(infcx, ty_alias);
            }
            fhir::ItemKind::Impl(impl_) => {
                self.check_impl(infcx, impl_);
            }
            fhir::ItemKind::Fn(fn_sig) => {
                self.check_fn_decl(infcx, fn_sig.decl);
            }
            fhir::ItemKind::OpaqueTy(opaque_ty) => {
                self.check_opaque_ty(infcx, opaque_ty);
            }
            fhir::ItemKind::Trait(_) => {}
        }
    }

    fn check_trait_item(&mut self, infcx: &mut InferCtxt, trait_item: &fhir::TraitItem) {
        match &trait_item.kind {
            fhir::TraitItemKind::Fn(fn_sig) => {
                self.check_fn_decl(infcx, fn_sig.decl);
            }
            fhir::TraitItemKind::Type(_) => {}
        }
    }

    fn check_impl_item(&mut self, infcx: &mut InferCtxt, impl_item: &fhir::ImplItem) {
        match &impl_item.kind {
            fhir::ImplItemKind::Fn(fn_sig) => {
                self.check_fn_decl(infcx, fn_sig.decl);
            }
            fhir::ImplItemKind::Type(_) => {}
        }
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
            let output = conv::conv_sort(self.genv, &assoc_reft.output, &mut bug_on_infer_sort);
            infcx
                .check_expr(&assoc_reft.body, &output)
                .collect_err(&mut self.errors);
        }
    }

    fn check_ty_alias(&mut self, infcx: &mut InferCtxt, ty_alias: &fhir::TyAlias) {
        self.check_type(infcx, &ty_alias.ty);
    }

    fn check_struct_def(&mut self, infcx: &mut InferCtxt, struct_def: &fhir::StructDef) {
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
            fhir::TyKind::Exists(_, ty) => {
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

fn visit_refine_params(node: &fhir::Node, f: impl FnMut(&fhir::RefineParam)) {
    struct RefineParamVisitor<F> {
        f: F,
    }

    impl<F> fhir::visit::Visitor for RefineParamVisitor<F>
    where
        F: FnMut(&fhir::RefineParam),
    {
        fn visit_refine_param(&mut self, param: &fhir::RefineParam) {
            (self.f)(param);
        }
    }
    RefineParamVisitor { f }.visit_node(node);
}
