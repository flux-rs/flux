#![warn(unused_extern_crates)]
#![feature(rustc_private, let_chains, box_patterns)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

mod annot_check;
mod conv;
mod wf;

use flux_common::{bug, dbg};
use flux_config as config;
use flux_errors::ResultExt;
use flux_macros::fluent_messages;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FluxLocalDefId},
    global_env::GlobalEnv,
    intern::List,
    queries::{Providers, QueryErr, QueryResult},
    rty::{self, fold::TypeFoldable},
    rustc::lowering,
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hir::{def::DefKind, def_id::LocalDefId, OwnerId};
use rustc_span::Symbol;

fluent_messages! { "../locales/en-US.ftl" }

pub fn build_genv<'sess, 'tcx>(
    early_cx: EarlyCtxt<'sess, 'tcx>,
) -> Result<GlobalEnv<'sess, 'tcx>, ErrorGuaranteed> {
    let func_decls = early_cx
        .map
        .func_decls()
        .map(|decl| (decl.name, conv::conv_func_decl(&early_cx, decl)))
        .collect();

    let genv = GlobalEnv::new(
        early_cx,
        func_decls,
        Providers {
            defns,
            qualifiers,
            check_wf,
            adt_def,
            type_of,
            variants_of,
            fn_sig,
            generics_of,
        },
    );
    check_crate_wf(&genv)?;
    Ok(genv)
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
    let qualifiers = genv
        .map()
        .qualifiers()
        .map(|qualifier| {
            let wfckresults = genv.check_wf(FluxLocalDefId::Flux(qualifier.name))?;
            normalize(genv, conv::conv_qualifier(genv, qualifier, &wfckresults))
        })
        .try_collect()?;
    println!("TRACE: rty::Qualifiers = {qualifiers:?}");
    Ok(qualifiers)
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

fn generics_of(genv: &GlobalEnv, local_id: LocalDefId) -> QueryResult<rty::Generics> {
    let def_id = local_id.to_def_id();
    let rustc_generics = lowering::lower_generics(genv.tcx.generics_of(def_id))
        .map_err(|err| QueryErr::unsupported(genv.tcx, def_id, err))?;
    let generics = genv.map().get_generics(local_id).unwrap_or_else(|| {
        genv.map()
            .get_generics(genv.tcx.local_parent(local_id))
            .unwrap()
    });
    Ok(conv::conv_generics(&rustc_generics, generics))
}

fn type_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::EarlyBinder<rty::PolyTy>> {
    let ty = match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias => {
            let alias = genv.map().get_type_alias(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            conv::expand_type_alias(genv, alias, &wfckresults)?
        }
        DefKind::TyParam => {
            match &genv.early_cx().get_generic_param(def_id).kind {
                fhir::GenericParamDefKind::Type { default: Some(ty) } => {
                    let wfckresults = genv.check_wf(def_id)?;
                    conv::conv_ty(genv, ty, &wfckresults)?
                }
                _ => bug!("non-type def"),
            }
        }
        kind => {
            bug!("`{:?}` not supported", kind.descr(def_id.to_def_id()))
        }
    };
    Ok(rty::EarlyBinder(ty))
}

fn variants_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::PolyVariants> {
    let variants = match genv.tcx.def_kind(def_id) {
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            let variants = conv::ConvCtxt::conv_enum_def_variants(genv, enum_def, &wfckresults)?
                .into_iter()
                .map(|variant| normalize(genv, variant))
                .try_collect()?;
            rty::Opaqueness::Transparent(variants)
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let wfckresults = genv.check_wf(def_id)?;
            conv::ConvCtxt::conv_struct_def_variant(genv, struct_def, &wfckresults)?
                .normalize(genv.defns()?)
                .map(|variant| List::from(vec![variant]))
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
    let fn_sig = conv::conv_fn_sig(genv, fn_sig, &wfckresults)?.normalize(genv.defns()?);
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx, def_id, "rty", &fn_sig).unwrap();
    }
    Ok(rty::EarlyBinder(fn_sig))
}

fn check_wf(genv: &GlobalEnv, flux_id: FluxLocalDefId) -> QueryResult<fhir::WfckResults> {
    match flux_id {
        FluxLocalDefId::Flux(sym) => check_wf_flux_item(genv, sym),
        FluxLocalDefId::Rust(def_id) => check_wf_rust_item(genv, def_id),
    }
}

fn check_wf_flux_item(genv: &GlobalEnv, sym: Symbol) -> QueryResult<fhir::WfckResults> {
    let wfckresults = match genv.map().get_flux_item(sym).unwrap() {
        fhir::FluxItem::Qualifier(qualifier) => wf::check_qualifier(genv.early_cx(), qualifier)?,
        fhir::FluxItem::Defn(defn) => wf::check_defn(genv.early_cx(), defn)?,
    };
    Ok(wfckresults)
}

fn check_wf_rust_item(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<fhir::WfckResults> {
    match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias => {
            let alias = genv.map().get_type_alias(def_id);
            let wfckresults = wf::check_ty_alias(genv.early_cx(), alias)?;
            annot_check::check_alias(genv.early_cx(), alias)?;
            Ok(wfckresults)
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let wfckresults = wf::check_struct_def(genv.early_cx(), struct_def)?;
            annot_check::check_struct_def(genv.early_cx(), struct_def)?;
            Ok(wfckresults)
        }
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let wfckresults = wf::check_enum_def(genv.early_cx(), enum_def)?;
            annot_check::check_enum_def(genv.early_cx(), enum_def)?;
            Ok(wfckresults)
        }
        DefKind::TyParam => {
            match &genv.early_cx().get_generic_param(def_id).kind {
                fhir::GenericParamDefKind::Type { default: Some(ty) } => {
                    let hir_id = genv.hir().local_def_id_to_hir_id(def_id);
                    let owner = genv.hir().get_parent_item(hir_id);
                    let wfckresults = wf::check_type(genv.early_cx(), ty, owner)?;
                    Ok(wfckresults)
                }
                fhir::GenericParamDefKind::Type { default: None } => {
                    bug!("type parameter without default")
                }
                _ => bug!("non-type def"),
            }
        }
        DefKind::Fn | DefKind::AssocFn => {
            let fn_sig = genv.map().get_fn_sig(def_id);
            let owner_id = OwnerId { def_id };
            let wf = wf::check_fn_sig(genv.early_cx(), fn_sig, owner_id)?;
            annot_check::check_fn_sig(genv.early_cx(), owner_id, fn_sig)?;
            Ok(wf)
        }
        kind => bug!("unexpected def kind `{kind:?}`"),
    }
}

fn check_crate_wf(genv: &GlobalEnv) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for def_id in genv.tcx.hir_crate_items(()).definitions() {
        match genv.tcx.def_kind(def_id) {
            DefKind::TyAlias | DefKind::Struct | DefKind::Enum | DefKind::Fn | DefKind::AssocFn => {
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
