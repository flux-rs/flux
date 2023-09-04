#![warn(unused_extern_crates)]
#![feature(rustc_private, min_specialization, box_patterns, lazy_cell, let_chains)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::{Binders, DesugarCtxt};
use flux_common::dbg;
use flux_config as config;
use flux_macros::fluent_messages;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod table_resolver;

pub use desugar::{
    desugar_defn, desugar_generics, desugar_qualifier, desugar_refined_by, func_def_to_func_decl,
};
use flux_middle::{
    fhir::{self, lift},
    global_env::GlobalEnv,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::OwnerId;

pub fn desugar_struct_def(
    genv: &GlobalEnv,
    owner_id: OwnerId,
    struct_def: surface::StructDef,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, owner_id.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;
    desugar::desugar_struct_def(genv, owner_id, struct_def)
}

pub fn desugar_enum_def(
    genv: &GlobalEnv,
    owner_id: OwnerId,
    enum_def: surface::EnumDef,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, owner_id.def_id)?;
    let enum_def = resolver.resolve_enum_def(enum_def)?;
    desugar::desugar_enum_def(genv, owner_id, &enum_def)
}

pub fn desugar_fn_sig(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    fn_sig: Option<surface::FnSig>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    if let Some(fn_sig) = fn_sig {
        let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, def_id)?;
        let fn_sig = resolver.resolve_fn_sig(fn_sig)?;

        let mut opaque_tys = FxHashMap::default();
        let mut cx = DesugarCtxt::new(genv, owner_id, Some(&mut opaque_tys));

        let generics = if let Some(generics) = &fn_sig.generics {
            cx.desugar_generics(generics)?
        } else {
            cx.as_lift_cx().lift_generics()?
        };
        genv.map().insert_generics(def_id, generics);

        let (generic_preds, fn_sig) = cx.desugar_fn_sig(&fn_sig, &mut Binders::new())?;

        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, def_id, "fhir", &fn_sig).unwrap();
        }

        genv.map_mut()
            .insert_generic_predicates(def_id, generic_preds);
        genv.map_mut().insert_fn_sig(def_id, fn_sig);
        genv.map_mut().insert_opaque_tys(opaque_tys);
    } else {
        let (generics, fn_info) = lift::lift_fn(genv.tcx, genv.sess, owner_id)?;
        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, def_id, "fhir", &fn_info.fn_sig).unwrap();
        }
        genv.map().insert_generics(def_id, generics);
        genv.map_mut()
            .insert_generic_predicates(def_id, fn_info.predicates);
        genv.map_mut().insert_fn_sig(def_id, fn_info.fn_sig);
        genv.map_mut().insert_opaque_tys(fn_info.opaque_tys);
    }
    Ok(())
}

pub fn desugar_sort_decl(sort_decl: surface::SortDecl) -> fhir::SortDecl {
    fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span }
}

pub fn desugar_type_alias(
    genv: &GlobalEnv,
    owner_id: OwnerId,
    alias: surface::TyAlias,
) -> Result<fhir::TyAlias, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, owner_id.def_id)?;
    let alias = resolver.resolve_type_alias(alias)?;
    desugar::desugar_type_alias(genv, owner_id, alias)
}
