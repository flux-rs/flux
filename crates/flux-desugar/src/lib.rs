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

    let generics = if let Some(generics) = &struct_def.generics {
        cx.desugar_generics(generics)?
    } else {
        cx.as_lift_cx().lift_generics()?
    }
    .with_refined_by(genv.map().refined_by(def_id));

    let predicates = cx.as_lift_cx().lift_generic_predicates()?;

    let struct_def = cx.desugar_struct_def(struct_def)?;
    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &struct_def).unwrap();
    }

    let map = genv.map_mut();
    map.insert_generics(def_id, generics);
    map.insert_generic_predicates(def_id, predicates);
    map.insert_struct(def_id, struct_def);

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

    let generics = if let Some(generics) = &enum_def.generics {
        cx.desugar_generics(generics)?
    } else {
        cx.as_lift_cx().lift_generics()?
    }
    .with_refined_by(genv.map().refined_by(def_id));
    let predicates = cx.as_lift_cx().lift_generic_predicates()?;

    let enum_def = cx.desugar_enum_def(enum_def)?;
    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &enum_def).unwrap();
    }

    let map = genv.map_mut();
    map.insert_generics(def_id, generics);
    map.insert_generic_predicates(def_id, predicates);
    map.insert_enum(def_id, enum_def);

    Ok(())
}

pub fn desugar_type_alias(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    ty_alias: Option<&surface::TyAlias>,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    if let Some(ty_alias) = ty_alias {
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);

        let generics = cx.as_lift_cx().lift_generics()?;
        let predicates = cx.as_lift_cx().lift_generic_predicates()?;

        let ty_alias = cx.desugar_type_alias(ty_alias)?;

        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, owner_id, "fhir", &ty_alias).unwrap();
        }

        let map = genv.map_mut();
        map.insert_generics(def_id, generics);
        map.insert_generic_predicates(def_id, predicates);
        map.insert_type_alias(def_id, ty_alias);
    } else {
        let (generics, predicates, ty_alias) =
            lift::lift_type_alias(genv.tcx, genv.sess, owner_id)?;

        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, owner_id, "fhir", &ty_alias).unwrap();
        }

        let map = genv.map_mut();
        map.insert_generics(def_id, generics);
        map.insert_generic_predicates(def_id, predicates);
        map.insert_type_alias(def_id, ty_alias);
    }

    Ok(())
}

pub fn desugar_fn_sig(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    fn_sig: Option<&surface::FnSig>,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    if let Some(fn_sig) = fn_sig {
        let mut opaque_tys = Default::default();
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, Some(&mut opaque_tys));

        let generics = if let Some(generics) = &fn_sig.generics {
            cx.desugar_generics(generics)?
        } else {
            cx.as_lift_cx().lift_generics()?
        };

        let (generic_preds, fn_sig) = cx.desugar_fn_sig(fn_sig)?;

        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, def_id, "fhir", &fn_sig).unwrap();
        }

        let map = genv.map_mut();
        map.insert_generics(def_id, generics);
        map.insert_generic_predicates(def_id, generic_preds);
        map.insert_fn_sig(def_id, fn_sig);
        map.insert_opaque_tys(opaque_tys);
    } else {
        let (generics, fn_info) = lift::lift_fn(genv.tcx, genv.sess, owner_id)?;
        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, def_id, "fhir", &fn_info.fn_sig).unwrap();
        }

        let map = genv.map_mut();
        map.insert_generics(def_id, generics);
        map.insert_generic_predicates(def_id, fn_info.predicates);
        map.insert_fn_sig(def_id, fn_info.fn_sig);
        map.insert_opaque_tys(fn_info.opaque_tys);
    }
    Ok(())
}

/// HACK(nilehmann) this is a bit of a hack. We use it to properly register generics and predicates
/// for items that don't have surface syntax (impl blocks, traits, ...), or for `impl` blocks with
/// explicit `generics` annotations. In the former case, we use `desugar`; in the latter cases we
/// just [lift] them from hir.
pub fn desugar_generics_and_predicates(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    resolver_output: &ResolverOutput,
    generics: Option<&surface::Generics>,
) -> Result<(), ErrorGuaranteed> {
    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let generics = if let Some(generics) = generics {
        cx.desugar_generics(generics)?
    } else {
        cx.as_lift_cx().lift_generics()?
    };
    let predicates = cx.as_lift_cx().lift_generic_predicates()?;

    let map = genv.map_mut();
    let def_id = owner_id.def_id;
    map.insert_generics(def_id, generics);
    map.insert_generic_predicates(def_id, predicates);

    Ok(())
}

pub fn desugar_sort_decl(sort_decl: &surface::SortDecl) -> fhir::SortDecl {
    fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span }
}
