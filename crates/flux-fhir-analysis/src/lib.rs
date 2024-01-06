#![feature(rustc_private, let_chains, box_patterns, if_let_guard, once_cell_try)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_type_ir;

mod annot_check;
mod conv;
mod wf;

use std::rc::Rc;

use flux_common::{bug, dbg};
use flux_config as config;
use flux_errors::ResultExt;
use flux_macros::fluent_messages;
use flux_middle::{
    fhir::{self, FluxLocalDefId, WfckResults},
    global_env::GlobalEnv,
    intern::List,
    queries::{Providers, QueryResult},
    rty::{self, fold::TypeFoldable, refining::Refiner},
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, def_id::LocalDefId, OwnerId};
use rustc_span::Symbol;

fluent_messages! { "../locales/en-US.ftl" }

pub fn provide(providers: &mut Providers) {
    *providers = Providers {
        defns,
        qualifiers,
        func_decls,
        check_wf,
        adt_def,
        type_of,
        variants_of,
        fn_sig,
        generics_of,
        refinement_generics_of,
        predicates_of,
        item_bounds,
    };
}

fn func_decls(genv: &GlobalEnv) -> FxHashMap<Symbol, rty::FuncDecl> {
    genv.map()
        .func_decls()
        .map(|decl| (decl.name, conv::conv_func_decl(genv, decl)))
        .collect()
}

fn defns(genv: &GlobalEnv) -> QueryResult<rty::Defns> {
    let defns = genv
        .map()
        .defns()
        .map(|defn| -> QueryResult<_> {
            let wfckresults = genv.check_wf(FluxLocalDefId::Flux(defn.name))?;
            let defn = conv::conv_defn(genv, defn, &wfckresults);
            Ok((defn.name, defn))
        })
        .try_collect()?;
    let defns = rty::Defns::new(defns).map_err(|cycle| {
        let span = genv.map().defn(cycle[0]).unwrap().expr.span;
        genv.sess
            .emit_err(errors::DefinitionCycle::new(span, cycle))
    })?;

    Ok(defns)
}

fn qualifiers(genv: &GlobalEnv) -> QueryResult<Vec<rty::Qualifier>> {
    genv.map()
        .qualifiers()
        .map(|qualifier| {
            let wfckresults = genv.check_wf(FluxLocalDefId::Flux(qualifier.name))?;
            normalize(genv, conv::conv_qualifier(genv, qualifier, &wfckresults))
        })
        .try_collect()
}

fn invariants_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<Vec<rty::Invariant>> {
    let (params, invariants) = match genv.tcx.def_kind(def_id) {
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            (&enum_def.params, &enum_def.invariants)
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            (&struct_def.params, &struct_def.invariants)
        }
        kind => bug!("expected struct or enum found `{kind:?}`"),
    };
    let wfckresults = genv.check_wf(def_id)?;
    conv::conv_invariants(genv, params, invariants, &wfckresults)
        .into_iter()
        .map(|invariant| normalize(genv, invariant))
        .collect()
}

fn adt_def(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::AdtDef> {
    let invariants = invariants_of(genv, def_id)?;
    match genv.tcx.def_kind(def_id) {
        DefKind::Enum => Ok(conv::adt_def_for_enum(genv, invariants, genv.map().get_enum(def_id))),
        DefKind::Struct => {
            Ok(conv::adt_def_for_struct(genv, invariants, genv.map().get_struct(def_id)))
        }
        kind => bug!("expected struct or enum found `{kind:?}`"),
    }
}

fn predicates_of(
    genv: &GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    let predicates = if let Some(predicates) = genv.map().get_generic_predicates(local_id) {
        let wfckresults = genv.check_wf(local_id)?;
        conv::conv_generic_predicates(genv, local_id, predicates, &wfckresults)?
    } else {
        rty::EarlyBinder(rty::GenericPredicates {
            parent: genv.tcx.opt_parent(local_id.to_def_id()),
            predicates: List::empty(),
        })
    };
    Ok(predicates)
}

fn item_bounds(
    genv: &GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::EarlyBinder<List<rty::Clause>>> {
    let wfckresults = genv.check_wf(local_id)?;
    let opaque_ty = genv.map().get_opaque_ty(local_id).unwrap();
    Ok(rty::EarlyBinder(conv::conv_opaque_ty(genv, local_id, opaque_ty, &wfckresults)?))
}

fn generics_of(genv: &GlobalEnv, local_id: LocalDefId) -> QueryResult<rty::Generics> {
    let def_id = local_id.to_def_id();
    let rustc_generics = genv.lower_generics_of(local_id)?;

    let def_kind = genv.tcx.def_kind(def_id);
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
    genv: &GlobalEnv,
    local_id: LocalDefId,
) -> QueryResult<rty::RefinementGenerics> {
    let parent = genv.tcx.generics_of(local_id).parent;
    let parent_count =
        if let Some(def_id) = parent { genv.refinement_generics_of(def_id)?.count() } else { 0 };
    match genv.tcx.def_kind(local_id) {
        DefKind::Fn | DefKind::AssocFn => {
            let fn_sig = genv.map().get_fn_sig(local_id);
            let wfckresults = genv.check_wf(local_id)?;
            let params = conv::conv_refinement_generics(genv, &fn_sig.params, &wfckresults);
            Ok(rty::RefinementGenerics { parent, parent_count, params })
        }
        _ => Ok(rty::RefinementGenerics { parent, parent_count, params: List::empty() }),
    }
}

fn type_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
    let ty = match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias { .. } => {
            let alias = genv.map().get_type_alias(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            conv::expand_type_alias(genv, alias, &wfckresults)?
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
            Refiner::default(genv, &generics).refine_poly_ty(&ty)?
        }
        kind => {
            bug!("`{:?}` not supported", kind.descr(def_id.to_def_id()))
        }
    };
    Ok(rty::EarlyBinder(ty))
}

fn variants_of(
    genv: &GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
    let variants = match genv.tcx.def_kind(def_id) {
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            let variants = conv::ConvCtxt::conv_enum_def_variants(genv, enum_def, &wfckresults)?
                .into_iter()
                .map(|variant| normalize(genv, variant))
                .try_collect()?;
            rty::Opaqueness::Transparent(rty::EarlyBinder(variants))
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            conv::ConvCtxt::conv_struct_def_variant(genv, struct_def, &wfckresults)?
                .normalize(genv.defns()?)
                .map(|variant| rty::EarlyBinder(List::singleton(variant)))
        }
        kind => {
            bug!("expected struct or enum found `{kind:?}`")
        }
    };
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx, def_id, "rty", &variants).unwrap();
    }
    Ok(variants)
}

fn fn_sig(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let fn_sig = genv.map().get_fn_sig(def_id);
    let wfckresults = genv.check_wf(def_id)?;
    let defns = genv.defns()?;
    let fn_sig = conv::conv_fn_sig(genv, def_id, fn_sig, &wfckresults)?
        .map(|fn_sig| fn_sig.normalize(defns));

    if config::dump_rty() {
        let generics = genv.generics_of(def_id)?;
        dbg::dump_item_info(genv.tcx, def_id, "rty", (generics, &fn_sig)).unwrap();
    }
    Ok(fn_sig)
}

fn check_wf(genv: &GlobalEnv, flux_id: FluxLocalDefId) -> QueryResult<Rc<fhir::WfckResults>> {
    match flux_id {
        FluxLocalDefId::Flux(sym) => check_wf_flux_item(genv, sym),
        FluxLocalDefId::Rust(def_id) => check_wf_rust_item(genv, def_id),
    }
}

fn check_wf_flux_item(genv: &GlobalEnv, sym: Symbol) -> QueryResult<Rc<fhir::WfckResults>> {
    let wfckresults = match genv.map().get_flux_item(sym).unwrap() {
        fhir::FluxItem::Qualifier(qualifier) => wf::check_qualifier(genv, qualifier)?,
        fhir::FluxItem::Defn(defn) => wf::check_defn(genv, defn)?,
    };
    Ok(Rc::new(wfckresults))
}

fn check_wf_rust_item(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<Rc<fhir::WfckResults>> {
    let wfckresults = match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias { .. } => {
            let alias = genv.map().get_type_alias(def_id);
            let mut wfckresults = wf::check_ty_alias(genv, alias)?;
            annot_check::check_alias(genv, &mut wfckresults, alias)?;
            wfckresults
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let mut wfckresults = wf::check_struct_def(genv, struct_def)?;
            annot_check::check_struct_def(genv, &mut wfckresults, struct_def)?;
            wfckresults
        }
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let mut wfckresults = wf::check_enum_def(genv, enum_def)?;
            annot_check::check_enum_def(genv, &mut wfckresults, enum_def)?;
            wfckresults
        }
        DefKind::Fn | DefKind::AssocFn => {
            let owner_id = OwnerId { def_id };
            let fn_sig = genv.map().get_fn_sig(def_id);
            let mut wfckresults = wf::check_fn_sig(genv, fn_sig, owner_id)?;
            annot_check::check_fn_sig(genv, &mut wfckresults, owner_id, fn_sig)?;
            wfckresults
        }
        DefKind::OpaqueTy => {
            let owner_id = OwnerId { def_id };
            let opaque_ty = genv.map().get_opaque_ty(def_id).unwrap();
            wf::check_opaque_ty(genv, opaque_ty, owner_id)?
        }
        DefKind::Impl { .. } => {
            // We currently dont support refinements on an impl item, so there's nothing to check here.
            WfckResults::new(OwnerId { def_id })
        }
        DefKind::Closure | DefKind::Coroutine | DefKind::TyParam => {
            let parent = genv.tcx.local_parent(def_id);
            return genv.check_wf(parent);
        }
        kind => panic!("unexpected def kind `{kind:?}`"),
    };
    Ok(Rc::new(wfckresults))
}

pub fn check_crate_wf(genv: &GlobalEnv) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for def_id in genv.tcx.hir_crate_items(()).definitions() {
        match genv.tcx.def_kind(def_id) {
            DefKind::TyAlias { .. }
            | DefKind::Struct
            | DefKind::Enum
            | DefKind::Fn
            | DefKind::AssocFn
            | DefKind::OpaqueTy => {
                err = genv.check_wf(def_id).emit(genv.sess).err().or(err);
            }
            _ => {}
        }
    }

    for defn in genv.map().defns() {
        err = genv
            .check_wf(FluxLocalDefId::Flux(defn.name))
            .emit(genv.sess)
            .err()
            .or(err);
    }

    for qualifier in genv.map().qualifiers() {
        err = genv
            .check_wf(FluxLocalDefId::Flux(qualifier.name))
            .emit(genv.sess)
            .err()
            .or(err);
    }

    let qualifiers = genv.map().qualifiers().map(|q| q.name).collect();
    for (_, fn_quals) in genv.map().fn_quals() {
        err = wf::check_fn_quals(genv.sess, &qualifiers, fn_quals)
            .err()
            .or(err);
    }

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}

fn normalize<T: TypeFoldable>(genv: &GlobalEnv, t: T) -> QueryResult<T> {
    Ok(t.normalize(genv.defns()?))
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
