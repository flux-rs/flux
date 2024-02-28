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

pub(crate) fn check_flux_item<'genv>(
    genv: GlobalEnv<'genv, '_>,
    item: &fhir::FluxItem,
) -> Result<WfckResults<'genv>> {
    let owner = FluxOwnerId::Flux(item.name());
    let mut infcx = InferCtxt::new(genv, owner);
    match item {
        fhir::FluxItem::Qualifier(qualifier) => {
            infcx.insert_params(qualifier.args);
            infcx.check_expr(&qualifier.expr, &rty::Sort::Bool)?;
        }
        fhir::FluxItem::Func(func) => {
            if let Some(body) = &func.body {
                infcx.insert_params(func.args);
                let output = conv::conv_sort(genv, &func.sort, &mut bug_on_infer_sort);
                infcx.check_expr(body, &output)?;
            }
        }
    }
    Ok(infcx.into_results())
}

pub(crate) fn check_node<'genv>(
    genv: GlobalEnv<'genv, '_>,
    node: &fhir::Node,
) -> Result<WfckResults<'genv>> {
    let mut infcx = InferCtxt::new(genv, node.owner_id().into());

    insert_params(&mut infcx, node)?;

    ImplicitParamInferer::infer(&mut infcx, node)?;

    Wf::check(&mut infcx, node)?;

    resolve_params(&mut infcx, node)?;

    param_usage::check(&infcx, node)?;

    Ok(infcx.into_results())
}

/// Initializes the inference context with all parameters required to check node
fn insert_params(infcx: &mut InferCtxt, node: &fhir::Node) -> Result {
    if let fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::OpaqueTy(..), owner_id, .. }) = node
    {
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

struct Wf<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> Wf<'a, 'genv, 'tcx> {
    fn check(infcx: &'a mut InferCtxt<'genv, 'tcx>, node: &fhir::Node) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut vis = Wf { infcx, errors };
        vis.visit_node(node);
        vis.errors.into_result()
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
}

impl fhir::visit::Visitor for Wf<'_, '_, '_> {
    fn visit_impl_assoc_reft(&mut self, assoc_reft: &fhir::ImplAssocReft) {
        let output = conv::conv_sort(self.infcx.genv, &assoc_reft.output, &mut bug_on_infer_sort);
        self.infcx
            .check_expr(&assoc_reft.body, &output)
            .collect_err(&mut self.errors);
    }

    fn visit_struct_def(&mut self, struct_def: &fhir::StructDef) {
        for invariant in struct_def.invariants {
            self.infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }
        fhir::visit::walk_struct_def(self, struct_def);
    }

    fn visit_enum_def(&mut self, enum_def: &fhir::EnumDef) {
        for invariant in enum_def.invariants {
            self.infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }
        fhir::visit::walk_enum_def(self, enum_def);
    }

    fn visit_variant_ret(&mut self, ret: &fhir::VariantRet) {
        let bty = &ret.bty;
        let expected = self
            .infcx
            .genv
            .sort_of_bty(bty)
            .unwrap_or_else(|| span_bug!(bty.span, "unrefinable base type: `{bty:?}`"));
        self.infcx
            .check_refine_arg(&ret.idx, &expected)
            .collect_err(&mut self.errors);
    }

    fn visit_fn_decl(&mut self, decl: &fhir::FnDecl) {
        fhir::visit::walk_fn_decl(self, decl);
        self.check_output_locs(decl);
    }

    fn visit_constraint(&mut self, constraint: &fhir::Constraint) {
        match constraint {
            fhir::Constraint::Type(loc, ty) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
                self.visit_ty(ty);
            }
            fhir::Constraint::Pred(pred) => {
                self.infcx
                    .check_expr(pred, &rty::Sort::Bool)
                    .collect_err(&mut self.errors);
            }
        }
    }

    fn visit_ty(&mut self, ty: &fhir::Ty) {
        match &ty.kind {
            fhir::TyKind::Indexed(bty, idx) => {
                if let Some(expected) = self.infcx.genv.sort_of_bty(bty) {
                    self.infcx
                        .check_refine_arg(idx, &expected)
                        .collect_err(&mut self.errors);
                } else if idx.is_colon_param().is_none() {
                    self.errors
                        .emit(errors::RefinedUnrefinableType::new(bty.span));
                }
                self.visit_bty(bty);
            }
            fhir::TyKind::Ptr(_, loc) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
            }
            fhir::TyKind::Constr(pred, ty) => {
                self.visit_ty(ty);
                self.infcx
                    .check_expr(pred, &rty::Sort::Bool)
                    .collect_err(&mut self.errors);
            }
            _ => fhir::visit::walk_ty(self, ty),
        }
    }

    fn visit_path(&mut self, path: &fhir::Path) {
        if let fhir::Res::Def(DefKind::TyAlias, def_id) = path.res {
            let Some(generics) = self
                .infcx
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
                self.infcx
                    .check_refine_arg(arg, &param.sort)
                    .collect_err(&mut self.errors);
            }
        }
        fhir::visit::walk_path(self, path);
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
