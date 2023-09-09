//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]
//!
//! # NOTE
//!
//! Desugaring requires knowing the sort of each type so we can correctly resolve binders declared with
//! @ syntax or arg syntax. In particular, to know the sort of a type parameter we need to know its
//! kind because only type parameters of sort `base` can be refined. The essential function implementing
//! this logic is [`GlobalEnv::sort_of_res`]. This function requires the generics for the item being
//! desugared to be register in [`fhir::Map`], thus we need to make sure that when desugaring an item,
//! generics are registered before desugaring the rest of the item.

#![warn(unused_extern_crates)]
#![feature(rustc_private, min_specialization, box_patterns, lazy_cell, let_chains)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::{Binders, DesugarCtxt};
use flux_common::{dbg, index::IndexGen};
use flux_config as config;
use flux_macros::fluent_messages;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod table_resolver;

pub use desugar::{desugar_defn, desugar_qualifier, desugar_refined_by, func_def_to_func_decl};
use flux_middle::{
    fhir::{
        self,
        lift::{self, LiftCtxt},
    },
    global_env::GlobalEnv,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::OwnerId;

pub fn desugar_struct_def(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    struct_def: surface::StructDef,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;

    let mut cx = DesugarCtxt::new(genv, owner_id, None);

    let (generics, predicates) = cx.as_lift_cx().lift_generics_with_predicates()?;
    // See crate level comment
    genv.map().insert_generics(def_id, generics);

    let struct_def = cx.desugar_struct_def(struct_def, &mut Binders::new())?;
    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &struct_def).unwrap();
    }
    genv.map_mut().insert_generic_predicates(def_id, predicates);
    genv.map_mut().insert_struct(def_id, struct_def);

    Ok(())
}

pub fn desugar_enum_def(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    enum_def: surface::EnumDef,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, owner_id.def_id)?;
    let enum_def = resolver.resolve_enum_def(enum_def)?;

    let mut cx = DesugarCtxt::new(genv, owner_id, None);

    let (generics, predicates) = cx.as_lift_cx().lift_generics_with_predicates()?;
    // See crate level comment
    genv.map().insert_generics(def_id, generics);

    let enum_def = cx.desugar_enum_def(&enum_def, &mut Binders::new())?;
    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx, owner_id, "fhir", &enum_def).unwrap();
    }
    genv.map_mut().insert_generic_predicates(def_id, predicates);
    genv.map_mut().insert_enum(def_id, enum_def);

    Ok(())
}

pub fn desugar_type_alias(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
    ty_alias: Option<surface::TyAlias>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    if let Some(ty_alias) = ty_alias {
        let resolver = table_resolver::Resolver::new(genv.tcx, genv.sess, def_id)?;
        let ty_alias = resolver.resolve_type_alias(ty_alias)?;

        let mut cx = DesugarCtxt::new(genv, owner_id, None);

        let (generics, predicates) = cx.as_lift_cx().lift_generics_with_predicates()?;
        // See crate level comment
        genv.map().insert_generics(def_id, generics);

        let ty_alias = cx.desugar_type_alias(ty_alias, &mut Binders::new())?;
        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, owner_id, "fhir", &ty_alias).unwrap();
        }
        genv.map_mut().insert_generic_predicates(def_id, predicates);
        genv.map_mut().insert_type_alias(def_id, ty_alias);
    } else {
        let (generics, predicates, ty_alias) =
            lift::lift_type_alias(genv.tcx, genv.sess, owner_id)?;
        if config::dump_fhir() {
            dbg::dump_item_info(genv.tcx, owner_id, "fhir", &ty_alias).unwrap();
        }
        genv.map().insert_generics(def_id, generics);
        genv.map_mut().insert_generic_predicates(def_id, predicates);
        genv.map_mut().insert_type_alias(def_id, ty_alias);
    }

    Ok(())
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

        let mut opaque_tys = Default::default();
        let mut cx = DesugarCtxt::new(genv, owner_id, Some(&mut opaque_tys));

        let generics = if let Some(generics) = &fn_sig.generics {
            cx.desugar_generics(generics)?
        } else {
            cx.as_lift_cx().lift_generics()?
        };
        // See crate level comment
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

/// HACK(nilehmann) this is a bit of a hack we use it to properly register generics and predicates
/// for items that don't have surface syntax (impl blocks, traits). In this cases we just [lift] them
/// from hir.
pub fn desugar_generics_and_predicates(
    genv: &mut GlobalEnv,
    owner_id: OwnerId,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    let local_id_gen = IndexGen::new();
    let (generics, predicates) = LiftCtxt::new(genv.tcx, genv.sess, owner_id, &local_id_gen, None)
        .lift_generics_with_predicates()?;
    genv.map().insert_generics(def_id, generics);
    genv.map_mut().insert_generic_predicates(def_id, predicates);
    Ok(())
}

pub fn desugar_sort_decl(sort_decl: surface::SortDecl) -> fhir::SortDecl {
    fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span }
}
