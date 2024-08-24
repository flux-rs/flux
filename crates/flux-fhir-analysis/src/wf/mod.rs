//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod param_usage;
mod sortck;

use std::iter;

use flux_common::result::{ErrorCollector, ResultExt as _};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{self, visit::Visitor, FluxOwnerId},
    global_env::GlobalEnv,
    rty::{self, WfckResults},
};
use rustc_data_structures::unord::UnordSet;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_span::{symbol::Ident, Symbol};

use self::sortck::{ImplicitParamInferer, InferCtxt};
use crate::conv::{self, bug_on_infer_sort};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn check_flux_item(genv: GlobalEnv, item: &fhir::FluxItem) -> Result<WfckResults> {
    let owner = FluxOwnerId::Flux(item.name());
    let mut infcx = InferCtxt::new(genv, owner);
    match item {
        fhir::FluxItem::Qualifier(qualifier) => {
            infcx.insert_params(qualifier.args)?;
            infcx.check_expr(&qualifier.expr, &rty::Sort::Bool)?;
        }
        fhir::FluxItem::Func(func) => {
            if let Some(body) = &func.body {
                infcx.insert_params(func.args)?;
                let output =
                    conv::conv_sort(genv, &func.sort, &mut bug_on_infer_sort).emit(&genv)?;
                infcx.check_expr(body, &output)?;
            }
        }
    }
    Ok(infcx.into_results())
}

pub(crate) fn check_node<'genv>(
    genv: GlobalEnv<'genv, '_>,
    node: &fhir::Node<'genv>,
) -> Result<WfckResults> {
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
    let genv = infcx.genv;
    if let fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::OpaqueTy(..), owner_id, .. }) = node
    {
        let parent = genv.tcx().local_parent(owner_id.def_id);
        if let Some(generics) = genv.map().get_generics(parent).emit(&genv)? {
            let wfckresults = genv.check_wf(parent).emit(&genv)?;
            for param in generics.refinement_params {
                let sort = wfckresults.node_sorts().get(param.fhir_id).unwrap().clone();
                infcx.insert_param(param.id, sort, param.kind);
            }
        }
    }
    visit_refine_params(node, |param| {
        let sort =
            conv::conv_sort(infcx.genv, &param.sort, &mut || infcx.next_sort_var()).emit(&genv)?;
        infcx.insert_param(param.id, sort, param.kind);
        Ok(())
    })
}

/// Check that all params with [`fhir::Sort::Infer`] have a sort inferred and save it in the [`WfckResults`]
fn resolve_params(infcx: &mut InferCtxt, node: &fhir::Node) -> Result {
    visit_refine_params(node, |param| infcx.resolve_param_sort(param))
}

pub(crate) fn check_fn_quals(
    sess: &FluxSession,
    qualifiers: &UnordSet<Symbol>,
    fn_quals: &[Ident],
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
    fn check(infcx: &'a mut InferCtxt<'genv, 'tcx>, node: &fhir::Node<'genv>) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut vis = Wf { infcx, errors };
        vis.visit_node(node);
        vis.errors.into_result()
    }

    fn check_output_locs(&mut self, fn_decl: &fhir::FnDecl) {
        let mut output_locs = FxHashSet::default();
        for ens in fn_decl.output.ensures {
            if let fhir::Ensures::Type(loc, ..) = ens
                && let (_, id) = loc.res.expect_param()
                && !output_locs.insert(id)
            {
                self.errors.emit(errors::DuplicatedEnsures::new(loc));
            }
        }

        for ty in fn_decl.inputs {
            if let fhir::TyKind::StrgRef(_, loc, _) = ty.kind
                && let (_, id) = loc.res.expect_param()
                && !output_locs.contains(&id)
            {
                self.errors.emit(errors::MissingEnsures::new(loc));
            }
        }
    }
}

impl<'genv> fhir::visit::Visitor<'genv> for Wf<'_, 'genv, '_> {
    fn visit_impl_assoc_reft(&mut self, assoc_reft: &fhir::ImplAssocReft) {
        let Ok(output) =
            conv::conv_sort(self.infcx.genv, &assoc_reft.output, &mut bug_on_infer_sort)
                .emit(&self.errors)
        else {
            return;
        };
        self.infcx
            .check_expr(&assoc_reft.body, &output)
            .collect_err(&mut self.errors);
    }

    fn visit_struct_def(&mut self, struct_def: &fhir::StructDef<'genv>) {
        for invariant in struct_def.invariants {
            self.infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }
        fhir::visit::walk_struct_def(self, struct_def);
    }

    fn visit_enum_def(&mut self, enum_def: &fhir::EnumDef<'genv>) {
        for invariant in enum_def.invariants {
            self.infcx
                .check_expr(invariant, &rty::Sort::Bool)
                .collect_err(&mut self.errors);
        }

        fhir::visit::walk_enum_def(self, enum_def);
    }

    fn visit_variant_ret(&mut self, ret: &fhir::VariantRet) {
        let genv = self.infcx.genv;
        let enum_id = ret.enum_id;
        let Ok(adt_sort_def) = genv.adt_sort_def_of(enum_id).emit(&self.errors) else { return };
        let Ok(args) = rty::GenericArgs::identity_for_item(genv, enum_id).emit(&self.errors) else {
            return;
        };
        let expected = adt_sort_def.sort(&args);
        self.infcx
            .check_refine_arg(&ret.idx, &expected)
            .collect_err(&mut self.errors);
    }

    fn visit_fn_decl(&mut self, decl: &fhir::FnDecl<'genv>) {
        fhir::visit::walk_fn_decl(self, decl);
        self.check_output_locs(decl);
    }

    fn visit_requires(&mut self, requires: &fhir::Requires<'genv>) {
        self.infcx
            .check_expr(&requires.pred, &rty::Sort::Bool)
            .collect_err(&mut self.errors);
    }

    fn visit_ensures(&mut self, ensures: &fhir::Ensures<'genv>) {
        match ensures {
            fhir::Ensures::Type(loc, ty) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
                self.visit_ty(ty);
            }
            fhir::Ensures::Pred(pred) => {
                self.infcx
                    .check_expr(pred, &rty::Sort::Bool)
                    .collect_err(&mut self.errors);
            }
        }
    }

    fn visit_ty(&mut self, ty: &fhir::Ty<'genv>) {
        match &ty.kind {
            fhir::TyKind::Indexed(bty, idx) => {
                let Ok(sort_of_bty) = self.infcx.genv.sort_of_bty(bty).emit(&self.errors) else {
                    return;
                };
                if let Some(expected) = sort_of_bty {
                    self.infcx
                        .check_refine_arg(idx, &expected)
                        .collect_err(&mut self.errors);
                } else if idx.is_colon_param().is_none() {
                    self.errors
                        .emit(errors::RefinedUnrefinableType::new(bty.span));
                }
                self.visit_bty(bty);
            }
            fhir::TyKind::StrgRef(_, loc, ty) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
                self.visit_ty(ty);
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

    fn visit_path(&mut self, path: &fhir::Path<'genv>) {
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

fn visit_refine_params(node: &fhir::Node, f: impl FnMut(&fhir::RefineParam) -> Result) -> Result {
    struct RefineParamVisitor<F> {
        f: F,
        err: Option<ErrorGuaranteed>,
    }

    impl<F> fhir::visit::Visitor<'_> for RefineParamVisitor<F>
    where
        F: FnMut(&fhir::RefineParam) -> Result,
    {
        fn visit_refine_param(&mut self, param: &fhir::RefineParam) {
            (self.f)(param).collect_err(&mut self.err);
        }
    }
    let mut visitor = RefineParamVisitor { f, err: None };
    visitor.visit_node(node);
    visitor.err.into_result()
}
