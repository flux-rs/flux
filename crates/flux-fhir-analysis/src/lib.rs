#![feature(rustc_private, let_chains, box_patterns, if_let_guard, once_cell_try, never_type)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod conv;
mod wf;

use std::rc::Rc;

use conv::{struct_compat, AfterSortck, ConvPhase};
use flux_common::{bug, dbg, iter::IterExt, result::ResultExt};
use flux_config as config;
use flux_errors::Errors;
use flux_macros::fluent_messages;
use flux_middle::{
    fhir::{self},
    global_env::GlobalEnv,
    queries::{Providers, QueryErr, QueryResult},
    query_bug,
    rty::{
        self,
        fold::TypeFoldable,
        refining::{self, Refiner},
        WfckResults,
    },
    MaybeExternId,
};
use flux_rustc_bridge::lowering::Lower;
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_span::Symbol;

fluent_messages! { "../locales/en-US.ftl" }

pub fn provide(providers: &mut Providers) {
    providers.spec_func_defns = spec_func_defns;
    providers.spec_func_decl = spec_func_decl;
    providers.qualifiers = qualifiers;
    providers.adt_sort_def_of = adt_sort_def_of;
    providers.check_wf = check_wf;
    providers.adt_def = adt_def;
    providers.constant_info = constant_info;
    providers.type_of = type_of;
    providers.variants_of = variants_of;
    providers.fn_sig = fn_sig;
    providers.generics_of = generics_of;
    providers.refinement_generics_of = refinement_generics_of;
    providers.predicates_of = predicates_of;
    providers.assoc_refinements_of = assoc_refinements_of;
    providers.sort_of_assoc_reft = sort_of_assoc_reft;
    providers.assoc_refinement_def = assoc_refinement_def;
    providers.default_assoc_refinement_def = default_assoc_refinement_def;
    providers.item_bounds = item_bounds;
}

fn adt_sort_def_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtSortDef> {
    let def_id = genv.maybe_extern_id(def_id);
    let kind = genv.map().refinement_kind(def_id.local_id())?;
    conv::conv_adt_sort_def(genv, def_id, kind)
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
            Ok(conv::conv_qualifier(genv, qualifier, &wfckresults)?
                .normalize(genv.spec_func_defns()?))
        })
        .try_collect()
}

fn adt_def(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtDef> {
    let def_id = genv.maybe_extern_id(def_id);
    let item = genv.map().expect_item(def_id.local_id())?;
    let invariants = invariants_of(genv, item)?;

    let adt_def = genv.tcx().adt_def(def_id.resolved_id()).lower(genv.tcx());

    let is_opaque = matches!(item.kind, fhir::ItemKind::Struct(def) if def.is_opaque());

    Ok(rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id)?, invariants, is_opaque))
}

fn constant_info(genv: GlobalEnv, local_def_id: LocalDefId) -> QueryResult<rty::ConstantInfo> {
    let def_id = genv.maybe_extern_id(local_def_id);
    let node = genv.map().node(def_id.local_id())?;
    let owner = rustc_hir::OwnerId { def_id: local_def_id };
    let Some(sort) = genv.sort_of_def_id(owner.def_id.to_def_id()).emit(&genv)? else {
        return Ok(rty::ConstantInfo::Uninterpreted);
    };
    match node {
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::Const(Some(expr)), .. }) => {
            // for these constants we must check and use the expression
            let wfckresults = wf::check_constant_expr(genv, owner, expr, &sort)?;
            conv::conv_constant_expr(genv, local_def_id.to_def_id(), expr, sort, &wfckresults)
        }
        fhir::Node::Item(fhir::Item { kind: fhir::ItemKind::Const(None), .. })
        | fhir::Node::AnonConst
        | fhir::Node::TraitItem(fhir::TraitItem { kind: fhir::TraitItemKind::Const, .. })
        | fhir::Node::ImplItem(fhir::ImplItem { kind: fhir::ImplItemKind::Const, .. }) => {
            // for these constants we try to evaluate if they are integral and return uninterpreted if we fail
            conv::conv_constant(genv, local_def_id.to_def_id())
        }
        _ => Err(query_bug!(def_id.local_id(), "expected const item"))?,
    }
}

fn invariants_of(genv: GlobalEnv, item: &fhir::Item) -> QueryResult<Vec<rty::Invariant>> {
    let (params, invariants) = match &item.kind {
        fhir::ItemKind::Enum(enum_def) => (enum_def.params, enum_def.invariants),
        fhir::ItemKind::Struct(struct_def) => (struct_def.params, struct_def.invariants),
        _ => Err(query_bug!(item.owner_id.local_id(), "expected struct or enum"))?,
    };
    let wfckresults = wf::check_invariants(genv, item.owner_id, params, invariants)?;
    conv::conv_invariants(genv, item.owner_id.map(|it| it.def_id), params, invariants, &wfckresults)
}

fn predicates_of(
    genv: GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    let def_id = genv.maybe_extern_id(def_id);
    match genv.def_kind(def_id) {
        DefKind::Impl { .. }
        | DefKind::Struct
        | DefKind::Enum
        | DefKind::Union
        | DefKind::TyAlias { .. }
        | DefKind::AssocFn
        | DefKind::AssocTy
        | DefKind::Trait
        | DefKind::Fn => {
            let generics = genv
                .map()
                .get_generics(def_id.local_id())?
                .ok_or_else(|| query_bug!(def_id.local_id(), "no generics for {def_id:?}"))?;
            let wfckresults = genv.check_wf(def_id.local_id())?;
            AfterSortck::new(genv, &wfckresults)
                .into_conv_ctxt()
                .conv_generic_predicates(def_id, generics)
        }
        DefKind::OpaqueTy | DefKind::Closure => {
            Ok(rty::EarlyBinder(rty::GenericPredicates {
                parent: genv.tcx().predicates_of(def_id).parent,
                predicates: rty::List::empty(),
            }))
        }
        kind => {
            Err(query_bug!(
                def_id.local_id(),
                "predicates_of called on `{def_id:?}` with kind `{kind:?}`"
            ))?
        }
    }
}

fn assoc_refinements_of(
    genv: GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::AssocRefinements> {
    let local_id = genv.maybe_extern_id(local_id);
    let predicates = match &genv.map().expect_item(local_id.local_id())?.kind {
        fhir::ItemKind::Trait(trait_) => {
            trait_
                .assoc_refinements
                .iter()
                .map(|assoc_reft| {
                    rty::AssocRefinement {
                        container_def_id: local_id.resolved_id(),
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
                        container_def_id: local_id.resolved_id(),
                        name: assoc_reft.name,
                    }
                })
                .collect()
        }
        _ => Err(query_bug!(local_id.resolved_id(), "expected trait or impl"))?,
    };
    Ok(rty::AssocRefinements { items: predicates })
}

fn default_assoc_refinement_def(
    genv: GlobalEnv,
    trait_id: LocalDefId,
    name: Symbol,
) -> QueryResult<Option<rty::EarlyBinder<rty::Lambda>>> {
    let trait_id = genv.maybe_extern_id(trait_id);
    let assoc_reft = genv
        .map()
        .expect_item(trait_id.local_id())?
        .expect_trait()
        .find_assoc_reft(name);

    if let Some(assoc_reft) = assoc_reft {
        let Some(body) = assoc_reft.body else { return Ok(None) };
        let wfckresults = genv.check_wf(trait_id.local_id())?;
        let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
        let body = cx.conv_assoc_reft_body(assoc_reft.params, &body, &assoc_reft.output)?;
        Ok(Some(rty::EarlyBinder(body)))
    } else {
        Err(QueryErr::InvalidAssocReft { container_def_id: trait_id.resolved_id(), name })?
    }
}

fn impl_assoc_refinement_def(
    genv: GlobalEnv,
    impl_id: LocalDefId,
    name: Symbol,
) -> QueryResult<Option<rty::EarlyBinder<rty::Lambda>>> {
    let assoc_reft = genv
        .map()
        .expect_item(impl_id)?
        .expect_impl()
        .find_assoc_reft(name);

    if let Some(assoc_reft) = assoc_reft {
        let wfckresults = genv.check_wf(impl_id)?;
        let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
        let body =
            cx.conv_assoc_reft_body(assoc_reft.params, &assoc_reft.body, &assoc_reft.output)?;
        Ok(Some(rty::EarlyBinder(body)))
    } else {
        Ok(None)
    }
}

fn assoc_refinement_def(
    genv: GlobalEnv,
    impl_id: LocalDefId,
    name: Symbol,
) -> QueryResult<rty::EarlyBinder<rty::Lambda>> {
    let impl_id = genv.maybe_extern_id(impl_id);

    // First check if the assoc reft is defined in the impl
    if let Some(lam) = impl_assoc_refinement_def(genv, impl_id.local_id(), name)? {
        return Ok(lam);
    }

    // Else check if the assoc reft is defined in the trait
    if let Some(trait_id) = genv.tcx().trait_id_of_impl(impl_id.resolved_id())
        && let Some(lam) = genv.default_assoc_refinement_def(trait_id, name)?
    {
        return Ok(lam);
    }
    Err(QueryErr::InvalidAssocReft { container_def_id: impl_id.resolved_id(), name })
}

fn sort_of_assoc_reft(
    genv: GlobalEnv,
    def_id: LocalDefId,
    name: Symbol,
) -> QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>> {
    let def_id = genv.maybe_extern_id(def_id);
    match &genv.map().expect_item(def_id.local_id())?.kind {
        fhir::ItemKind::Trait(trait_) => {
            let Some(assoc_reft) = trait_.find_assoc_reft(name) else { return Ok(None) };
            let wfckresults = genv.check_wf(def_id.local_id())?;
            let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| cx.conv_sort(&p.sort))
                .try_collect_vec()?;
            let output = cx.conv_sort(&assoc_reft.output)?;
            Ok(Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output))))
        }
        fhir::ItemKind::Impl(impl_) => {
            let assoc_reft = impl_.find_assoc_reft(name).unwrap();
            let wfckresults = genv.check_wf(def_id.local_id())?;
            let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
            let inputs = assoc_reft
                .params
                .iter()
                .map(|p| cx.conv_sort(&p.sort))
                .try_collect_vec()?;
            let output = cx.conv_sort(&assoc_reft.output)?;
            Ok(Some(rty::EarlyBinder(rty::FuncSort::new(inputs, output))))
        }
        _ => Err(query_bug!(def_id.local_id(), "expected trait or impl")),
    }
}

fn item_bounds(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::Clauses>> {
    let def_id = genv.maybe_extern_id(def_id);
    let parent = genv.tcx().local_parent(def_id.local_id());
    let wfckresults = genv.check_wf(parent)?;
    let opaque_ty = genv.map().node(def_id.local_id())?.expect_opaque_ty();
    Ok(rty::EarlyBinder(
        AfterSortck::new(genv, &wfckresults)
            .into_conv_ctxt()
            .conv_opaque_ty(opaque_ty)?,
    ))
}

fn generics_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::Generics> {
    let def_id = genv.maybe_extern_id(def_id);

    let def_kind = genv.def_kind(def_id);
    let generics = match def_kind {
        DefKind::Impl { .. }
        | DefKind::Struct
        | DefKind::Enum
        | DefKind::Union
        | DefKind::TyAlias { .. }
        | DefKind::AssocFn
        | DefKind::AssocTy
        | DefKind::Trait
        | DefKind::Fn => {
            let is_trait = def_kind == DefKind::Trait;
            let generics = genv
                .map()
                .get_generics(def_id.local_id())?
                .ok_or_else(|| query_bug!(def_id.local_id(), "no generics for {def_id:?}"))?;
            conv::conv_generics(genv, generics, def_id, is_trait)
        }
        DefKind::OpaqueTy | DefKind::Closure => {
            let rustc_generics = genv.lower_generics_of(def_id);
            refining::refine_generics(genv, def_id.resolved_id(), &rustc_generics)?
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
) -> QueryResult<rty::EarlyBinder<rty::RefinementGenerics>> {
    let parent = genv.tcx().generics_of(local_id).parent;
    let parent_count =
        if let Some(def_id) = parent { genv.refinement_generics_of(def_id)?.count() } else { 0 };
    let generics = match genv.map().node(local_id)? {
        fhir::Node::Item(fhir::Item {
            kind: fhir::ItemKind::Fn(..) | fhir::ItemKind::TyAlias(..),
            generics,
            ..
        })
        | fhir::Node::TraitItem(fhir::TraitItem {
            kind: fhir::TraitItemKind::Fn(..),
            generics,
            ..
        })
        | fhir::Node::ImplItem(fhir::ImplItem {
            kind: fhir::ImplItemKind::Fn(..), generics, ..
        }) => {
            let wfckresults = genv.check_wf(local_id)?;
            let params = conv::conv_refinement_generics(generics.refinement_params, &wfckresults)?;
            rty::RefinementGenerics { parent, parent_count, own_params: params }
        }
        _ => rty::RefinementGenerics { parent, parent_count, own_params: rty::List::empty() },
    };
    Ok(rty::EarlyBinder(generics))
}

fn type_of(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::TyOrCtor>> {
    let def_id = genv.maybe_extern_id(def_id);
    let ty = match genv.def_kind(def_id) {
        DefKind::TyAlias { .. } => {
            let fhir_ty_alias = genv
                .map()
                .expect_item(def_id.local_id())?
                .expect_type_alias();
            let wfckresults = genv.check_wf(def_id.local_id())?;
            let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
            let ty_alias = cx.conv_type_alias(def_id, fhir_ty_alias)?;
            struct_compat::type_alias(genv, fhir_ty_alias, &ty_alias, def_id)?;
            rty::TyOrCtor::Ctor(ty_alias)
        }
        DefKind::TyParam => {
            match def_id {
                MaybeExternId::Local(local_id) => {
                    let owner = genv.hir().ty_param_owner(local_id);
                    let param = genv.map().get_generics(owner)?.unwrap().get_param(local_id);
                    match param.kind {
                        fhir::GenericParamKind::Type { default: Some(ty) } => {
                            let parent = genv.tcx().local_parent(local_id);
                            let wfckresults = genv.check_wf(parent)?;
                            conv::conv_default_type_parameter(genv, def_id, &ty, &wfckresults)?
                                .into()
                        }
                        k => Err(query_bug!(local_id, "non-type def def {k:?} {def_id:?}"))?,
                    }
                }
                MaybeExternId::Extern(_, extern_id) => {
                    let ty = genv.lower_type_of(extern_id)?.skip_binder();
                    Refiner::default_for_item(genv, ty_param_owner(genv, extern_id))?
                        .refine_ty_or_base(&ty)?
                        .into()
                }
            }
        }
        DefKind::Impl { .. } | DefKind::Struct | DefKind::Enum | DefKind::AssocTy => {
            let ty = genv.lower_type_of(def_id.local_id())?.skip_binder();
            Refiner::default_for_item(genv, def_id.resolved_id())?
                .refine_ty_or_base(&ty)?
                .into()
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

fn ty_param_owner(genv: GlobalEnv, def_id: DefId) -> DefId {
    let def_kind = genv.def_kind(def_id);
    match def_kind {
        DefKind::Trait | DefKind::TraitAlias => def_id,
        DefKind::LifetimeParam | DefKind::TyParam | DefKind::ConstParam => {
            genv.tcx().parent(def_id)
        }
        _ => bug!("ty_param_owner: {:?} is a {:?} not a type parameter", def_id, def_kind),
    }
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
            let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
            let variants = cx.conv_enum_variants(def_id, enum_def)?;
            println!("TRACE: conv_enum_variants {variants:?}");
            let variants = rty::List::from_vec(struct_compat::variants(genv, &variants, def_id)?);
            rty::Opaqueness::Transparent(rty::EarlyBinder(variants))
        }
        fhir::ItemKind::Struct(struct_def) => {
            let wfckresults = genv.check_wf(local_id)?;
            let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
            cx.conv_struct_variant(def_id, struct_def)?
                .map(|variant| -> QueryResult<_> {
                    let variants = struct_compat::variants(genv, &[variant], def_id)?;
                    Ok(rty::List::from_vec(variants))
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
    let fhir_fn_sig = genv
        .map()
        .expect_owner_node(def_id.local_id())?
        .fn_sig()
        .unwrap();
    let wfckresults = genv.check_wf(def_id.local_id())?;
    let fn_sig = AfterSortck::new(genv, &wfckresults)
        .into_conv_ctxt()
        .conv_fn_sig(def_id, fhir_fn_sig)?;
    let fn_sig = struct_compat::fn_sig(genv, fhir_fn_sig.decl, &fn_sig, def_id)?;

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
    Ok(rty::EarlyBinder(fn_sig))
}

fn check_wf(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<Rc<WfckResults>> {
    let node = genv.map().expect_owner_node(def_id)?;
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
