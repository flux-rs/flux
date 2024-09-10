#![feature(rustc_private, let_chains, box_patterns, if_let_guard, once_cell_try)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

pub mod compare_impl_item;
mod conv;
mod wf;

use std::rc::Rc;

use conv::bug_on_infer_sort;
use flux_common::{dbg, iter::IterExt, result::ResultExt};
use flux_config as config;
use flux_errors::Errors;
use flux_macros::fluent_messages;
use flux_middle::{
    fhir,
    global_env::GlobalEnv,
    intern::List,
    queries::{Providers, QueryErr, QueryResult},
    query_bug,
    rty::{self, fold::TypeFoldable, refining::Refiner, WfckResults},
    rustc::lowering,
};
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_span::Symbol;

fluent_messages! { "../locales/en-US.ftl" }

pub fn provide(providers: &mut Providers) {
    providers.spec_func_defns = spec_func_defns;
    providers.spec_func_decl = spec_func_decl;
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

fn adt_sort_def_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtSortDef> {
    conv::conv_adt_sort_def(genv, def_id, genv.map().refined_by(def_id)?)
}

fn spec_func_decl(genv: GlobalEnv, name: Symbol) -> QueryResult<rty::SpecFuncDecl> {
    if let Some(func) = genv.map().spec_func(name) {
        conv::conv_func_decl(genv, func)
    } else {
        let itf = flux_middle::THEORY_FUNCS.get(&name).unwrap();
        Ok(rty::SpecFuncDecl {
            name: itf.name,
            sort: itf.sort.clone(),
            kind: fhir::SpecFuncKind::Thy(itf.fixpoint_name),
        })
    }
}

fn spec_func_defns(genv: GlobalEnv) -> QueryResult<rty::SpecFuncDefns> {
    let mut defns = FxHashMap::default();

    // Collect and emit all errors
    let mut errors = Errors::new(genv.sess());
    for func in genv.map().spec_funcs() {
        let Some(wfckresults) = wf::check_fn_spec(genv, func).collect_err(&mut errors) else {
            continue;
        };
        let Ok(defn) = conv::conv_defn(genv, func, &wfckresults).emit(&errors) else {
            continue;
        };
        if let Some(defn) = defn {
            defns.insert(defn.name, defn);
        }
    }
    errors.into_result()?;

    let defns = rty::SpecFuncDefns::new(defns)
        .map_err(|cycle| {
            let span = genv.map().spec_func(cycle[0]).unwrap().body.unwrap().span;
            errors::DefinitionCycle::new(span, cycle)
        })
        .emit(&genv)?;

    Ok(defns)
}

fn qualifiers(genv: GlobalEnv) -> QueryResult<Vec<rty::Qualifier>> {
    genv.map()
        .qualifiers()
        .map(|qualifier| {
            let wfckresults = wf::check_qualifier(genv, qualifier)?;
            normalize(genv, conv::conv_qualifier(genv, qualifier, &wfckresults)?)
        })
        .try_collect()
}

fn invariants_of(genv: GlobalEnv, item: &fhir::Item) -> QueryResult<Vec<rty::Invariant>> {
    let (params, invariants) = match &item.kind {
        fhir::ItemKind::Enum(enum_def) => (&enum_def.params, &enum_def.invariants),
        fhir::ItemKind::Struct(struct_def) => (&struct_def.params, &struct_def.invariants),
        _ => Err(query_bug!(item.owner_id.local_id(), "expected struct or enum"))?,
    };
    let wfckresults = genv.check_wf(item.owner_id.local_id().def_id)?;
    conv::conv_invariants(
        genv,
        item.owner_id.map(|it| it.def_id),
        params,
        invariants,
        &wfckresults,
    )?
    .into_iter()
    .map(|invariant| normalize(genv, invariant))
    .collect()
}

fn adt_def(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtDef> {
    let def_id = genv.maybe_extern_id(def_id);
    let item = genv.map().expect_item(def_id.local_id())?;
    let invariants = invariants_of(genv, item)?;

    let adt_def = lowering::lower_adt_def(genv.tcx(), genv.tcx().adt_def(def_id.resolved_id()));

    let is_opaque = matches!(item.kind, fhir::ItemKind::Struct(def) if def.is_opaque());

    Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id)?, invariants, is_opaque))
}

fn predicates_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    if let Some(generics) = genv.map().get_generics(local_id)? {
        let wfckresults = genv.check_wf(local_id)?;
        conv::conv_generic_predicates(genv, local_id, generics.predicates, &wfckresults)
    } else {
        Ok(rty::EarlyBinder(rty::GenericPredicates {
            parent: genv.tcx().predicates_of(local_id.to_def_id()).parent,
            predicates: List::empty(),
        }))
    }
}

fn assoc_refinements_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::AssocRefinements> {
    let predicates = match &genv.map().expect_item(local_id)?.kind {
        fhir::ItemKind::Trait(trait_) => {
            trait_
                .assoc_refinements
                .iter()
                .map(|assoc_reft| {
                    rty::AssocRefinement {
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
                    rty::AssocRefinement {
                        container_def_id: local_id.to_def_id(),
                        name: assoc_reft.name,
                    }
                })
                .collect()
        }
        _ => Err(query_bug!(local_id, "expected trait or impl"))?,
    };
    Ok(rty::AssocRefinements { items: predicates })
}

fn assoc_refinement_def(
    genv: GlobalEnv,
    impl_id: LocalDefId,
    name: Symbol,
) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
    let assoc_reft = genv
        .map()
        .expect_item(impl_id)?
        .expect_impl()
        .find_assoc_reft(name);

    if let Some(assoc_reft) = assoc_reft {
        let wfckresults = genv.check_wf(impl_id)?;
        Ok(rty::EarlyBinder(conv::conv_assoc_reft_def(genv, assoc_reft, &wfckresults)?))
    } else {
        Err(QueryErr::InvalidAssocReft { impl_id: impl_id.to_def_id(), name })?
    }
}

fn sort_of_assoc_reft(
    genv: GlobalEnv,
    def_id: LocalDefId,
    name: Symbol,
) -> QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>> {
    match &genv.map().expect_item(def_id)?.kind {
        fhir::ItemKind::Trait(trait_) => {
            let Some(assoc_reft) = trait_.find_assoc_reft(name) else { return Ok(None) };
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| conv::resolve_param_sort(genv, p, None))
                .try_collect_vec()?;
            let output = conv::conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort)?;
            Ok(Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output))))
        }
        fhir::ItemKind::Impl(impl_) => {
            let assoc_reft = impl_.find_assoc_reft(name).unwrap();
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| conv::resolve_param_sort(genv, p, None))
                .try_collect_vec()?;
            let output = conv::conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort)?;
            Ok(Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output))))
        }
        _ => Err(query_bug!(def_id, "expected trait or impl")),
    }
}

fn item_bounds(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
    let wfckresults = genv.check_wf(local_id)?;
    let opaque_ty = genv.map().expect_item(local_id)?.expect_opaque_ty();
    Ok(rty::EarlyBinder(conv::conv_opaque_ty(genv, local_id, opaque_ty, &wfckresults)?))
}

fn generics_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::Generics> {
    let def_id = genv.maybe_extern_id(def_id);

    let def_kind = genv.def_kind(def_id);
    let generics = match def_kind {
        DefKind::Impl { .. }
        | DefKind::Struct
        | DefKind::Enum
        | DefKind::TyAlias { .. }
        | DefKind::OpaqueTy
        | DefKind::AssocFn
        | DefKind::AssocTy
        | DefKind::Trait
        | DefKind::Fn => {
            let is_trait = def_kind == DefKind::Trait;
            let generics = genv
                .map()
                .get_generics(def_id.local_id())?
                .ok_or_else(|| query_bug!(def_id.local_id(), "no generics for {def_id:?}"))?;
            conv::conv_generics(genv, generics, def_id, is_trait)?
        }
        DefKind::Closure => {
            let rustc_generics = genv.tcx().generics_of(def_id.local_id());
            rty::Generics {
                own_params: List::empty(),
                parent: rustc_generics.parent,
                parent_count: rustc_generics.parent_count,
                has_self: rustc_generics.has_self,
            }
        }
        kind => {
            Err(query_bug!(
                def_id.local_id(),
                "generics_of called on `{def_id:?}` with kind `{kind:?}`"
            ))?
        }
    };
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx(), def_id.resolved_id(), "generics.rty", &generics).unwrap();
    }
    Ok(generics)
}

fn refinement_generics_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::RefinementGenerics> {
    let parent = genv.tcx().generics_of(local_id).parent;
    let parent_count =
        if let Some(def_id) = parent { genv.refinement_generics_of(def_id)?.count() } else { 0 };
    match genv.map().node(local_id)? {
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::Fn(..), generics, .. })
        | fhir::Node::TraitItem(fhir::TraitItem {
            kind: fhir::TraitItemKind::Fn(..),
            generics,
            ..
        })
        | fhir::Node::ImplItem(fhir::ImplItem {
            kind: fhir::ImplItemKind::Fn(..), generics, ..
        }) => {
            let wfckresults = genv.check_wf(local_id)?;
            let params = conv::conv_refinement_generics(
                genv,
                generics.refinement_params,
                Some(&wfckresults),
            )?;
            Ok(rty::RefinementGenerics { parent, parent_count, params })
        }
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::TyAlias(..), generics, .. }) => {
            let params = conv::conv_refinement_generics(genv, generics.refinement_params, None)?;
            Ok(rty::RefinementGenerics { parent, parent_count, params })
        }
        _ => Ok(rty::RefinementGenerics { parent, parent_count, params: List::empty() }),
    }
}

fn type_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::TyCtor>> {
    let def_id = genv.maybe_extern_id(def_id);
    let ty = match genv.def_kind(def_id) {
        DefKind::TyAlias { .. } => {
            let alias = genv
                .map()
                .expect_item(def_id.local_id())?
                .expect_type_alias();
            let wfckresults = genv.check_wf(def_id.local_id())?;
            conv::expand_type_alias(genv, def_id, alias, &wfckresults)?
        }
        DefKind::TyParam => {
            match &genv.map().get_generic_param(def_id.local_id())?.kind {
                fhir::GenericParamKind::Type { default: Some(ty) } => {
                    let parent = genv.tcx().local_parent(def_id.local_id());
                    let wfckresults = genv.check_wf(parent)?;
                    conv::conv_ty(genv, ty, &wfckresults)?
                }
                k => Err(query_bug!(def_id.local_id(), "non-type def def {k:?} {def_id:?}"))?,
            }
        }
        DefKind::Impl { .. } | DefKind::Struct | DefKind::Enum | DefKind::AssocTy => {
            let generics = genv.generics_of(def_id)?;
            let ty = genv.lower_type_of(def_id.local_id())?.skip_binder();
            Refiner::default(genv, &generics).refine_ty_ctor(&ty)?
        }
        kind => {
            Err(query_bug!(
                def_id.local_id(),
                "`{:?}` not supported",
                kind.descr(def_id.resolved_id())
            ))?
        }
    };
    Ok(rty::EarlyBinder(ty))
}

fn variants_of(
    genv: GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
    let def_id = genv.maybe_extern_id(def_id);
    let local_id = def_id.local_id();

    let item = &genv.map().expect_item(local_id)?;
    let variants = match &item.kind {
        fhir::ItemKind::Enum(enum_def) => {
            let wfckresults = genv.check_wf(local_id)?;
            let variants =
                conv::ConvCtxt::conv_enum_variants(genv, def_id, enum_def, &wfckresults)?
                    .into_iter()
                    .map(|variant| normalize(genv, variant))
                    .try_collect()?;
            rty::Opaqueness::Transparent(rty::EarlyBinder(variants))
        }
        fhir::ItemKind::Struct(struct_def) => {
            let wfckresults = genv.check_wf(local_id)?;
            conv::ConvCtxt::conv_struct_variant(genv, def_id, struct_def, &wfckresults)?
                .map(|variants| {
                    variants
                        .into_iter()
                        .map(|variant| normalize(genv, variant))
                        .try_collect()
                })
                .transpose()?
                .map(rty::EarlyBinder)
        }
        _ => Err(query_bug!(def_id.local_id(), "expected struct or enum"))?,
    };
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx(), def_id.resolved_id(), "rty", &variants).unwrap();
    }
    Ok(variants)
}

fn fn_sig(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let def_id = genv.maybe_extern_id(def_id);
    let fn_sig = genv.desugar(def_id.local_id())?.fn_sig().unwrap();
    let wfckresults = genv.check_wf(def_id.local_id())?;
    let defns = genv.spec_func_defns()?;
    let fn_sig = conv::conv_fn_sig(genv, def_id, fn_sig, &wfckresults)?
        .map(|fn_sig| fn_sig.normalize(defns));

    if config::dump_rty() {
        let generics = genv.generics_of(def_id)?;
        let refinement_generics = genv.refinement_generics_of(def_id)?;
        dbg::dump_item_info(
            genv.tcx(),
            def_id.resolved_id(),
            "rty",
            (generics, refinement_generics, &fn_sig),
        )
        .unwrap();
    }
    Ok(fn_sig)
}

fn check_wf(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<Rc<WfckResults>> {
    let node = genv.desugar(def_id)?;
    let wfckresults = wf::check_node(genv, &node)?;
    Ok(Rc::new(wfckresults))
}

pub fn check_crate_wf(genv: GlobalEnv) -> Result<(), ErrorGuaranteed> {
    let mut errors = Errors::new(genv.sess());

    let qualifiers = genv.map().qualifiers().map(|q| q.name).collect();

    for def_id in genv.tcx().hir_crate_items(()).definitions() {
        if genv.ignored(def_id) || genv.is_dummy(def_id) {
            continue;
        }
        let def_kind = genv.def_kind(def_id);
        match def_kind {
            DefKind::TyAlias { .. }
            | DefKind::Struct
            | DefKind::Enum
            | DefKind::Fn
            | DefKind::AssocFn
            | DefKind::Trait
            | DefKind::Impl { .. }
            // we skip checking the DefKind::OpaqueTy because they
            // must be wf-checked (and desugared) in the context of
            // their "parent", so we do so "lazily" when the appropriate
            // query is called on the "parent"
            => {
                let _ = genv.check_wf(def_id).emit(&errors);
            }
            _ => {}
        }
        if matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            if let Ok(fn_quals) = genv.map().fn_quals_for(def_id).emit(&errors) {
                wf::check_fn_quals(genv.sess(), &qualifiers, fn_quals).collect_err(&mut errors);
            }
        }
    }

    // Query qualifiers and spec funcs to report wf errors
    let _ = genv.qualifiers().emit(&errors);
    let _ = genv.spec_func_defns().emit(&errors);

    errors.into_result()
}

fn normalize<T: TypeFoldable>(genv: GlobalEnv, t: T) -> QueryResult<T> {
    Ok(t.normalize(genv.spec_func_defns()?))
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_definition_cycle, code = E0999)]
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
