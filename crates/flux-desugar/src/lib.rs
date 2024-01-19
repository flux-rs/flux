//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]

#![feature(rustc_private, min_specialization, box_patterns, lazy_cell, let_chains)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::RustItemCtxt;
use flux_common::dbg;
use flux_config as config;
use flux_macros::fluent_messages;
use resolver::ResolverOutput;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;
mod sort_resolver;

pub use desugar::{desugar_defn, desugar_qualifier, desugar_refined_by, func_def_to_func_decl};
use flux_middle::{
    fhir::{self, lift},
    global_env::GlobalEnv,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::OwnerId;

pub fn desugar_struct_def(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    struct_def: &surface::StructDef,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let struct_def = cx.desugar_struct_def(struct_def)?;

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &struct_def).unwrap();
    }

    genv.map_mut().insert_struct(def_id, struct_def);

    Ok(())
}

pub fn desugar_enum_def(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    enum_def: &surface::EnumDef,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let enum_def = cx.desugar_enum_def(enum_def)?;

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &enum_def).unwrap();
    }

    genv.map_mut().insert_enum(def_id, enum_def);

    Ok(())
}

pub fn desugar_type_alias(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    ty_alias: Option<&surface::TyAlias>,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let ty_alias = if let Some(ty_alias) = ty_alias {
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
        cx.desugar_type_alias(ty_alias)?
    } else {
        lift::lift_type_alias(genv.tcx, genv.sess, owner_id)?
    };

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &ty_alias).unwrap();
    }

    genv.map_mut().insert_type_alias(def_id, ty_alias);

    Ok(())
}

pub fn desugar_fn_sig(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    fn_sig: Option<&surface::FnSig>,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let (fn_sig, opaque_tys) = if let Some(fn_sig) = fn_sig {
        let mut opaque_tys = Default::default();
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, Some(&mut opaque_tys));

        let fn_sig = cx.desugar_fn_sig(fn_sig)?;

        (fn_sig, opaque_tys)
    } else {
        lift::lift_fn(genv.tcx, genv.sess, owner_id)?
    };

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, def_id, "fhir", &fn_sig).unwrap();
    }

    let map = genv.map_mut();
    map.insert_fn_sig(def_id, fn_sig);
    map.insert_opaque_tys(opaque_tys);

    Ok(())
}

pub fn desugar_trait_or_impl(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    resolver_output: &ResolverOutput,
    trait_or_impl: &surface::TraitOrImpl,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let trait_or_impl = cx.desugar_trait_or_impl(trait_or_impl)?;

    genv.map_mut().insert_trait_or_impl(def_id, trait_or_impl);

    Ok(())
}

pub fn desugar_sort_decl(sort_decl: &surface::SortDecl) -> fhir::SortDecl {
    fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span }
}
