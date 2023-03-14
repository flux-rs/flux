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
use flux_macros::fluent_messages;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir,
    global_env::{GlobalEnv, Queries, QueryResult},
    rty::{self, fold::TypeFoldable},
    rustc,
};
use itertools::Itertools;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, FatalError, SubdiagnosticMessage};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use wf::Wf;

fluent_messages! { "../locales/en-US.ftl" }

pub fn build_genv<'sess, 'tcx>(
    early_cx: EarlyCtxt<'sess, 'tcx>,
) -> Result<GlobalEnv<'sess, 'tcx>, ErrorGuaranteed> {
    check_crate(&early_cx)?;

    let adt_defs = conv_adt_defs(&early_cx);
    let defns = conv_defns(&early_cx)?;
    let qualifiers = early_cx
        .map
        .qualifiers()
        .map(|qualifier| conv::conv_qualifier(&early_cx, qualifier).normalize(&defns))
        .collect();
    let uifs = early_cx
        .map
        .uifs()
        .map(|uif| (uif.name, conv::conv_uif(&early_cx, uif)))
        .collect();

    let mut genv = GlobalEnv::new(
        early_cx,
        adt_defs,
        defns,
        qualifiers,
        uifs,
        Queries { type_of, variants, fn_sig },
    );
    register_generics(&mut genv);

    Ok(genv)
}

fn type_of(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::Binder<rty::Ty>> {
    match genv.tcx.def_kind(def_id) {
        DefKind::TyAlias => {
            let alias = genv.map().get_type_alias(def_id);
            conv::expand_type_alias(genv, alias)
        }
        DefKind::TyParam => {
            match &genv.early_cx().get_generic_param(def_id).kind {
                fhir::GenericParamDefKind::Type { default: Some(ty) } => conv::conv_ty(genv, ty),
                _ => bug!("non-type def"),
            }
        }
        kind => {
            bug!("`{:?}` not supported", kind.descr(def_id.to_def_id()))
        }
    }
}

fn variants(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::PolyVariants> {
    match genv.tcx.def_kind(def_id) {
        DefKind::Enum => {
            let enum_def = genv.map().get_enum(def_id);
            let variants = conv::ConvCtxt::conv_enum_def_variants(genv, enum_def)?
                .into_iter()
                .map(|variant| variant.normalize(genv.defns()))
                .collect();
            Ok(rty::Opaqueness::Transparent(variants))
        }
        DefKind::Struct => {
            let struct_def = genv.map().get_struct(def_id);
            let variants = conv::ConvCtxt::conv_struct_def_variant(genv, struct_def)?
                .map(|variant| vec![variant.normalize(genv.defns())]);
            Ok(variants)
        }
        kind => {
            bug!("expected struct or enum found `{kind:?}`")
        }
    }
}

fn fn_sig(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<rty::PolySig> {
    let fn_sig = genv.map().get_fn_sig(def_id);
    let fn_sig = conv::conv_fn_sig(genv, fn_sig)?.normalize(genv.defns());
    if config::dump_rty() {
        dbg::dump_item_info(genv.tcx, def_id, "rty", &fn_sig).unwrap();
    }
    Ok(fn_sig)
}

fn conv_adt_defs(early_cx: &EarlyCtxt) -> FxHashMap<DefId, rty::AdtDef> {
    let mut map = FxHashMap::default();
    for struct_def in early_cx.map.structs() {
        map.insert(struct_def.def_id.to_def_id(), conv::adt_def_for_struct(early_cx, struct_def));
    }
    for enum_def in early_cx.map.enums() {
        map.insert(enum_def.def_id.to_def_id(), conv::adt_def_for_enum(early_cx, enum_def));
    }

    map
}

fn conv_defns(early_cx: &EarlyCtxt) -> Result<rty::Defns, ErrorGuaranteed> {
    let defns = early_cx
        .map
        .defns()
        .map(|defn| (defn.name, conv::conv_defn(early_cx, defn)))
        .collect();
    rty::Defns::new(defns).map_err(|cycle| {
        let span = early_cx.map.defn(cycle[0]).unwrap().expr.span;
        early_cx
            .sess
            .emit_err(errors::DefinitionCycle::new(span, cycle))
    })
}

fn check_crate(early_cx: &EarlyCtxt) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for defn in early_cx.map.defns() {
        err = Wf::check_defn(early_cx, defn).err().or(err);
    }

    for qualifier in early_cx.map.qualifiers() {
        err = Wf::check_qualifier(early_cx, qualifier).err().or(err);
    }

    for alias in early_cx.map.type_aliases() {
        err = Wf::check_alias(early_cx, alias)
            .and_then(|_| annot_check::check_alias(early_cx, alias))
            .err()
            .or(err);
    }

    for struct_def in early_cx.map.structs() {
        err = Wf::check_struct_def(early_cx, struct_def)
            .and_then(|_| annot_check::check_struct_def(early_cx, struct_def))
            .err()
            .or(err);
    }

    for enum_def in early_cx.map.enums() {
        err = Wf::check_enum_def(early_cx, enum_def)
            .and_then(|_| annot_check::check_enum_def(early_cx, enum_def))
            .err()
            .or(err);
    }

    for (def_id, fn_sig) in early_cx.map.fn_sigs() {
        err = Wf::check_fn_sig(early_cx, fn_sig)
            .and_then(|_| annot_check::check_fn_sig(early_cx, def_id, fn_sig))
            .err()
            .or(err);
    }

    let qualifiers = early_cx.map.qualifiers().map(|q| q.name.clone()).collect();
    for (_, fn_quals) in early_cx.map.fn_quals() {
        err = Wf::check_fn_quals(early_cx.sess, &qualifiers, fn_quals)
            .err()
            .or(err);
    }

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}

fn register_generics(genv: &mut GlobalEnv) {
    let generics = genv
        .map()
        .generics()
        .map(|(def_id, generics)| {
            let rustc_generics = rustc::lowering::lower_generics(
                genv.tcx,
                genv.sess,
                genv.tcx.generics_of(def_id.to_def_id()),
            )
            .unwrap_or_else(|_| FatalError.raise());
            (def_id.to_def_id(), conv::conv_generics(&rustc_generics, generics))
        })
        .collect_vec();
    genv.register_generics(generics);
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
