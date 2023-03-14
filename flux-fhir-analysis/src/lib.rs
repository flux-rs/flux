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
    fhir,
    global_env::GlobalEnv,
    intern::List,
    queries::{Providers, QueryErr, QueryResult},
    rty::{self, fold::TypeFoldable},
    rustc::lowering,
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use wf::Wf;

fluent_messages! { "../locales/en-US.ftl" }

pub fn build_genv<'sess, 'tcx>(
    early_cx: EarlyCtxt<'sess, 'tcx>,
) -> Result<GlobalEnv<'sess, 'tcx>, ErrorGuaranteed> {
    let uifs = early_cx
        .map
        .uifs()
        .map(|uif| (uif.name, conv::conv_uif(&early_cx, uif)))
        .collect();

    let genv = GlobalEnv::new(
        early_cx,
        uifs,
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
            let defn = conv::conv_defn(genv.early_cx(), defn);
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
        .map(|qualifier| normalize(genv, conv::conv_qualifier(genv.early_cx(), qualifier)))
        .try_collect()
}

fn adt_def(genv: &GlobalEnv, def_id: LocalDefId) -> rty::AdtDef {
    match genv.tcx.def_kind(def_id) {
        DefKind::Enum => conv::adt_def_for_enum(genv.early_cx(), genv.map().get_enum(def_id)),
        DefKind::Struct => conv::adt_def_for_struct(genv.early_cx(), genv.map().get_struct(def_id)),
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

fn type_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::Binder<rty::Ty>> {
    match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias => {
            let alias = genv.map().get_type_alias(def_id);
            let wfresults = genv.check_wf(def_id)?;
            conv::expand_type_alias(genv, alias, &wfresults)
        }
        DefKind::TyParam => {
            match &genv.early_cx().get_generic_param(def_id).kind {
                fhir::GenericParamDefKind::Type { default: Some(ty) } => {
                    let wfresults = todo!();
                    conv::conv_ty(genv, ty, &wfresults)
                }
                _ => bug!("non-type def"),
            }
        }
        kind => {
            bug!("`{:?}` not supported", kind.descr(def_id.to_def_id()))
        }
    }
}

fn variants_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::PolyVariants> {
    match genv.tcx.def_kind(def_id) {
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let wfresults = genv.check_wf(def_id)?;
            let variants = conv::ConvCtxt::conv_enum_def_variants(genv, enum_def, &wfresults)?
                .into_iter()
                .map(|variant| normalize(genv, variant))
                .try_collect()?;
            Ok(rty::Opaqueness::Transparent(variants))
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let wfresults = genv.check_wf(def_id)?;
            let variants = conv::ConvCtxt::conv_struct_def_variant(genv, struct_def, &wfresults)?
                .normalize(genv.defns()?)
                .map(|variant| List::from(vec![variant]));
            Ok(variants)
        }
        kind => {
            bug!("expected struct or enum found `{kind:?}`")
        }
    }
}

fn fn_sig(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::PolySig> {
    let fn_sig = genv.map().get_fn_sig(def_id);
    let wfresults = genv.check_wf(def_id)?;
    let fn_sig = conv::conv_fn_sig(genv, fn_sig, &wfresults)?.normalize(genv.defns()?);
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx, def_id, "rty", &fn_sig).unwrap();
    }
    Ok(fn_sig)
}

fn check_wf(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<fhir::WfResults> {
    match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias => {
            let alias = genv.map().get_type_alias(def_id);
            let wf = Wf::check_alias(genv.early_cx(), alias)?;
            annot_check::check_alias(genv.early_cx(), alias)?;
            Ok(wf)
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let wf = Wf::check_struct_def(genv.early_cx(), struct_def)?;
            annot_check::check_struct_def(genv.early_cx(), struct_def)?;
            Ok(wf)
        }
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let wf = Wf::check_enum_def(genv.early_cx(), enum_def)?;
            annot_check::check_enum_def(genv.early_cx(), enum_def)?;
            Ok(wf)
        }
        DefKind::Fn | DefKind::AssocFn => {
            let fn_sig = genv.map().get_fn_sig(def_id);
            let wf = Wf::check_fn_sig(genv.early_cx(), fn_sig)?;
            annot_check::check_fn_sig(genv.early_cx(), def_id, fn_sig)?;
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
        err = Wf::check_defn(genv.early_cx(), defn).err().or(err);
    }

    for qualifier in genv.map().qualifiers() {
        err = Wf::check_qualifier(genv.early_cx(), qualifier)
            .err()
            .or(err);
    }

    let qualifiers = genv.map().qualifiers().map(|q| q.name.clone()).collect();
    for (_, fn_quals) in genv.map().fn_quals() {
        err = Wf::check_fn_quals(genv.sess, &qualifiers, fn_quals)
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
