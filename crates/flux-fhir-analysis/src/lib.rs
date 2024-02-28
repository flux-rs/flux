#![feature(rustc_private, let_chains, box_patterns, if_let_guard, once_cell_try)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_type_ir;

mod annot_check;
pub mod compare_impl_item;
mod conv;
mod wf;

use std::rc::Rc;

use conv::bug_on_infer_sort;
use flux_common::{bug, dbg, result::ResultExt};
use flux_config as config;
use flux_errors::Errors;
use flux_macros::fluent_messages;
use flux_middle::{
    fhir::{self, FluxLocalDefId},
    global_env::GlobalEnv,
    intern::List,
    queries::{Providers, QueryResult},
    rty::{self, fold::TypeFoldable, refining::Refiner, WfckResults},
    rustc::lowering,
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_span::Symbol;

fluent_messages! { "../locales/en-US.ftl" }

pub fn provide(providers: &mut Providers) {
    providers.spec_func_defns = spec_func_defns;
    providers.spec_func_decls = spec_func_decls;
    providers.qualifiers = qualifiers;
    providers.adt_sort_def_of = adt_sort_def_of;
    providers.check_wf = check_wf;
    providers.adt_def = adt_def;
    providers.type_of = type_of;
    providers.variants_of = variants_of;
    providers.fn_sig = fn_sig;
    providers.generics_of = generics_of;
    providers.refinement_generics_of = refinement_generics_of;
    providers.predicates_of = predicates_of;
    providers.assoc_refinements_of = assoc_refinements_of;
    providers.sort_of_assoc_reft = sort_of_assoc_reft;
    providers.assoc_refinement_def = assoc_refinement_def;
    providers.item_bounds = item_bounds;
}

fn adt_sort_def_of(genv: GlobalEnv, def_id: LocalDefId) -> rty::AdtSortDef {
    conv::conv_adt_sort_def(genv, def_id, genv.map().refined_by(def_id))
}

fn spec_func_decls(genv: GlobalEnv) -> FxHashMap<Symbol, rty::SpecFuncDecl> {
    let mut func_decls = FxHashMap::default();
    for func in genv.map().spec_funcs() {
        func_decls.insert(func.name, conv::conv_func_decl(genv, func));
    }
    for itf in flux_middle::theory_funcs() {
        let func_decl = rty::SpecFuncDecl {
            name: itf.name,
            sort: itf.sort.clone(),
            kind: fhir::SpecFuncKind::Thy(itf.fixpoint_name),
        };
        func_decls.insert(itf.name, func_decl);
    }

    func_decls
}

fn spec_func_defns(genv: GlobalEnv) -> QueryResult<rty::SpecFuncDefns> {
    let mut defns = FxHashMap::default();
    for func in genv.map().spec_funcs() {
        let wfckresults = genv.check_wf(FluxLocalDefId::Flux(func.name))?;
        if let Some(defn) = conv::conv_defn(genv, func, &wfckresults)? {
            defns.insert(defn.name, defn);
        }
    }
    let defns = rty::SpecFuncDefns::new(defns).map_err(|cycle| {
        let span = genv.map().spec_func(cycle[0]).unwrap().body.unwrap().span;
        genv.sess()
            .emit_err(errors::DefinitionCycle::new(span, cycle))
    })?;

    Ok(defns)
}

fn qualifiers(genv: GlobalEnv) -> QueryResult<Vec<rty::Qualifier>> {
    genv.map()
        .qualifiers()
        .map(|qualifier| {
            let wfckresults = genv.check_wf(FluxLocalDefId::Flux(qualifier.name))?;
            normalize(genv, conv::conv_qualifier(genv, qualifier, &wfckresults)?)
        })
        .try_collect()
}

fn invariants_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<Vec<rty::Invariant>> {
    let (params, invariants) = match &genv.map().expect_item(def_id).kind {
        fhir::ItemKind::Enum(enum_def) => (&enum_def.params, &enum_def.invariants),
        fhir::ItemKind::Struct(struct_def) => (&struct_def.params, &struct_def.invariants),
        _ => bug!("expected struct or enum"),
    };
    let wfckresults = genv.check_wf(def_id)?;
    conv::conv_invariants(genv, def_id, params, invariants, &wfckresults)?
        .into_iter()
        .map(|invariant| normalize(genv, invariant))
        .collect()
}

fn adt_def(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtDef> {
    let invariants = invariants_of(genv, def_id)?;
    let item = genv.map().expect_item(def_id);

    let adt_def = if let Some(extern_id) = item.extern_id {
        lowering::lower_adt_def(&genv.tcx().adt_def(extern_id))
    } else {
        lowering::lower_adt_def(&genv.tcx().adt_def(item.owner_id))
    };

    let is_opaque = matches!(item.kind, fhir::ItemKind::Struct(def) if def.is_opaque());

    Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), invariants, is_opaque))
}

fn predicates_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    if let Some(generics) = genv.map().get_generics(local_id) {
        let wfckresults = genv.check_wf(local_id)?;
        conv::conv_generic_predicates(genv, local_id, generics.predicates, &wfckresults)
    } else {
        Ok(rty::EarlyBinder(rty::GenericPredicates {
            parent: genv.tcx().predicates_of(local_id.to_def_id()).parent,
            predicates: List::empty(),
        }))
    }
}

fn assoc_refinements_of(genv: GlobalEnv, local_id: LocalDefId) -> rty::AssocPredicates {
    let predicates = match &genv.map().expect_item(local_id).kind {
        fhir::ItemKind::Trait(trait_) => {
            trait_
                .assoc_refinements
                .iter()
                .map(|assoc_reft| {
                    rty::AssocPredicate {
                        container_def_id: local_id.to_def_id(),
                        name: assoc_reft.name,
                    }
                })
                .collect()
        }
        fhir::ItemKind::Impl(impl_) => {
            impl_
                .assoc_refinements
                .iter()
                .map(|assoc_reft| {
                    rty::AssocPredicate {
                        container_def_id: local_id.to_def_id(),
                        name: assoc_reft.name,
                    }
                })
                .collect()
        }
        _ => {
            bug!("expected trait or impl");
        }
    };
    rty::AssocPredicates { predicates }
}

fn assoc_refinement_def(
    genv: GlobalEnv,
    impl_id: LocalDefId,
    name: Symbol,
) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
    let assoc_reft = genv
        .map()
        .expect_item(impl_id)
        .expect_impl()
        .find_assoc_reft(name)
        .unwrap();
    let wfckresults = genv.check_wf(impl_id)?;
    Ok(rty::EarlyBinder(conv::conv_assoc_reft_def(genv, assoc_reft, &wfckresults)?))
}

fn sort_of_assoc_reft(
    genv: GlobalEnv,
    def_id: LocalDefId,
    name: Symbol,
) -> Option<rty::EarlyBinder<rty::FuncSort>> {
    match &genv.map().expect_item(def_id).kind {
        fhir::ItemKind::Trait(trait_) => {
            let assoc_reft = trait_.find_assoc_reft(name)?;
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| conv::resolve_param_sort(genv, p, None))
                .collect_vec();
            let output = conv::conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort);
            Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output)))
        }
        fhir::ItemKind::Impl(impl_) => {
            let assoc_reft = impl_.find_assoc_reft(name).unwrap();
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| conv::resolve_param_sort(genv, p, None))
                .collect_vec();
            let output = conv::conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort);
            Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output)))
        }
        _ => {
            bug!("expected trait or impl");
        }
    }
}

fn item_bounds(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
    let wfckresults = genv.check_wf(local_id)?;
    let opaque_ty = genv.map().expect_item(local_id).expect_opaque_ty();
    Ok(rty::EarlyBinder(conv::conv_opaque_ty(genv, local_id, opaque_ty, &wfckresults)?))
}

fn generics_of(genv: GlobalEnv, local_id: LocalDefId) -> QueryResult<rty::Generics> {
    let def_id = local_id.to_def_id();
    let rustc_generics = genv.lower_generics_of(local_id)?;

    let def_kind = genv.def_kind(def_id);
    match def_kind {
        DefKind::Impl { .. }
        | DefKind::Struct
        | DefKind::Enum
        | DefKind::TyAlias { .. }
        | DefKind::OpaqueTy
        | DefKind::AssocFn
        | DefKind::AssocTy
        | DefKind::Trait
        | DefKind::Fn => {
            let is_trait = (def_kind == DefKind::Trait).then_some(local_id);
            let generics = genv
                .map()
                .get_generics(local_id)
                .unwrap_or_else(|| bug!("no generics for {:?}", def_id));
            conv::conv_generics(&rustc_generics, generics, is_trait)
        }
        DefKind::Closure | DefKind::Coroutine => {
            Ok(rty::Generics {
                params: List::empty(),
                parent: rustc_generics.parent(),
                parent_count: rustc_generics.parent_count(),
            })
        }
        kind => bug!("generics_of called on `{def_id:?}` with kind `{kind:?}`"),
    }
}

fn refinement_generics_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::RefinementGenerics> {
    let parent = genv.tcx().generics_of(local_id).parent;
    let parent_count =
        if let Some(def_id) = parent { genv.refinement_generics_of(def_id)?.count() } else { 0 };
    match genv.map().node(local_id) {
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::Fn(fn_sig), .. })
        | fhir::Node::TraitItem(fhir::TraitItem {
            kind: fhir::TraitItemKind::Fn(fn_sig), ..
        })
        | fhir::Node::ImplItem(fhir::ImplItem { kind: fhir::ImplItemKind::Fn(fn_sig), .. }) => {
            let wfckresults = genv.check_wf(local_id)?;
            let params = conv::conv_refinement_generics(
                genv,
                fn_sig.decl.generics.refinement_params,
                Some(&wfckresults),
            );
            Ok(rty::RefinementGenerics { parent, parent_count, params })
        }
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::TyAlias(ty_alias), .. }) => {
            let params =
                conv::conv_refinement_generics(genv, ty_alias.generics.refinement_params, None);
            Ok(rty::RefinementGenerics { parent, parent_count, params })
        }
        _ => Ok(rty::RefinementGenerics { parent, parent_count, params: List::empty() }),
    }
}

fn type_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::TyCtor>> {
    let ty = match genv.def_kind(def_id) {
        DefKind::TyAlias { .. } => {
            let alias = genv.map().expect_item(def_id).expect_type_alias();
            let wfckresults = genv.check_wf(def_id)?;
            conv::expand_type_alias(genv, def_id.to_def_id(), alias, &wfckresults)?
        }
        DefKind::TyParam => {
            match &genv.get_generic_param(def_id).kind {
                fhir::GenericParamKind::Type { default: Some(ty) } => {
                    let wfckresults = genv.check_wf(def_id)?;
                    conv::conv_ty(genv, ty, &wfckresults)?
                }
                k => bug!("non-type def {k:?} {def_id:?}"),
            }
        }
        DefKind::Impl { .. } | DefKind::Struct | DefKind::Enum | DefKind::AssocTy => {
            let generics = genv.generics_of(def_id)?;
            let ty = genv.lower_type_of(def_id)?.skip_binder();
            Refiner::default(genv, &generics).refine_ty_ctor(&ty)?
        }
        kind => {
            bug!("`{:?}` not supported", kind.descr(def_id.to_def_id()))
        }
    };
    Ok(rty::EarlyBinder(ty))
}

fn variants_of(
    genv: GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
    let item = &genv.map().expect_item(def_id);
    let variants = match &item.kind {
        fhir::ItemKind::Enum(enum_def) => {
            let wfckresults = genv.check_wf(def_id)?;
            let variants = conv::ConvCtxt::conv_enum_def_variants(
                genv,
                def_id.to_def_id(),
                enum_def,
                &wfckresults,
            )?
            .into_iter()
            .map(|variant| normalize(genv, variant))
            .try_collect()?;
            rty::Opaqueness::Transparent(rty::EarlyBinder(variants))
        }
        fhir::ItemKind::Struct(struct_def) => {
            let wfckresults = genv.check_wf(def_id)?;
            conv::ConvCtxt::conv_struct_def_variant(
                genv,
                def_id.to_def_id(),
                struct_def,
                &wfckresults,
            )?
            .normalize(genv.spec_func_defns()?)
            .map(|variant| rty::EarlyBinder(List::singleton(variant)))
        }
        _ => bug!("expected struct or enum"),
    };
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx(), def_id, "rty", &variants).unwrap();
    }
    Ok(variants)
}

fn fn_sig(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let fn_sig = genv.map().node(def_id).fn_sig().unwrap();
    let wfckresults = genv.check_wf(def_id)?;
    let defns = genv.spec_func_defns()?;
    let fn_sig = conv::conv_fn_decl(genv, def_id, fn_sig.decl, &wfckresults)?
        .map(|fn_sig| fn_sig.normalize(defns));

    if config::dump_rty() {
        let generics = genv.generics_of(def_id)?;
        let refinement_generics = genv.refinement_generics_of(def_id)?;
        dbg::dump_item_info(genv.tcx(), def_id, "rty", (generics, refinement_generics, &fn_sig))
            .unwrap();
    }
    Ok(fn_sig)
}

fn check_wf<'genv>(
    genv: GlobalEnv<'genv, '_>,
    flux_id: FluxLocalDefId,
) -> QueryResult<Rc<WfckResults<'genv>>> {
    let wfckresults = match flux_id {
        FluxLocalDefId::Flux(sym) => {
            wf::check_flux_item(genv, genv.map().get_flux_item(sym).unwrap())?
        }
        FluxLocalDefId::Rust(def_id) => {
            let def_kind = genv.def_kind(def_id);
            if matches!(def_kind, DefKind::Closure | DefKind::Coroutine | DefKind::TyParam) {
                let parent = genv.tcx().local_parent(def_id);
                return genv.check_wf(parent);
            }
            let node = genv.map().node(def_id);
            let mut wfckresults = wf::check_node(genv, &node)?;
            annot_check::check_node(genv, &mut wfckresults, &node)?;
            wfckresults
        }
    };
    Ok(Rc::new(wfckresults))
}

pub fn check_crate_wf(genv: GlobalEnv) -> Result<(), ErrorGuaranteed> {
    let mut errors = Errors::new(genv.sess());

    let qualifiers = genv.map().qualifiers().map(|q| q.name).collect();

    for def_id in genv.tcx().hir_crate_items(()).definitions() {
        let def_kind = genv.def_kind(def_id);
        match def_kind {
            DefKind::TyAlias { .. }
            | DefKind::Struct
            | DefKind::Enum
            | DefKind::Fn
            | DefKind::AssocFn
            | DefKind::OpaqueTy => {
                let _ = genv.check_wf(def_id).emit(&errors).ok();
            }
            _ => {}
        }
        if matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            let fn_quals = genv.map().fn_quals_for(def_id);
            wf::check_fn_quals(genv.sess(), &qualifiers, fn_quals).collect_err(&mut errors);
        }
    }

    for defn in genv.map().spec_funcs() {
        let _ = genv
            .check_wf(FluxLocalDefId::Flux(defn.name))
            .emit(&errors)
            .ok();
    }

    for qualifier in genv.map().qualifiers() {
        let _ = genv
            .check_wf(FluxLocalDefId::Flux(qualifier.name))
            .emit(&errors)
            .ok();
    }

    errors.into_result()
}

fn normalize<T: TypeFoldable>(genv: GlobalEnv, t: T) -> QueryResult<T> {
    Ok(t.normalize(genv.spec_func_defns()?))
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_definition_cycle, code = "FLUX")]
    pub struct DefinitionCycle {
        #[primary_span]
        #[label]
        span: Span,
        msg: String,
    }

    impl DefinitionCycle {
        pub(super) fn new(span: Span, cycle: Vec<Symbol>) -> Self {
            let root = format!("`{}`", cycle[0]);
            let names: Vec<String> = cycle.iter().map(|s| format!("`{s}`")).collect();
            let msg = format!("{} -> {}", names.join(" -> "), root);
            Self { span, msg }
        }
    }
}
