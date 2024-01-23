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
use rustc_data_structures::unord::ExtendUnord;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;
mod sort_resolver;

pub use desugar::{desugar_defn, desugar_qualifier, func_def_to_func_decl};
use flux_middle::{
    fhir::{self, lift},
    global_env::GlobalEnv,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::OwnerId;

pub fn desugar_struct_def<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    struct_def: &surface::StructDef,
    resolver_output: &ResolverOutput,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let (struct_def, refined_by) = cx.desugar_struct_def(struct_def)?;

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx(), owner_id, "fhir", struct_def).unwrap();
    }

    fhir.structs.insert(def_id, genv.alloc(struct_def));
    fhir.refined_by.insert(def_id, genv.alloc(refined_by));

    Ok(())
}

pub fn desugar_enum_def<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    enum_def: &surface::EnumDef,
    resolver_output: &ResolverOutput,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let (enum_def, refined_by) = cx.desugar_enum_def(enum_def)?;

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx(), owner_id, "fhir", &enum_def).unwrap();
    }

    fhir.enums.insert(def_id, genv.alloc(enum_def));
    fhir.refined_by.insert(def_id, genv.alloc(refined_by));

    Ok(())
}

pub fn desugar_type_alias<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    ty_alias: Option<&surface::TyAlias>,
    resolver_output: &ResolverOutput,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let (ty_alias, refined_by) = if let Some(ty_alias) = ty_alias {
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
        cx.desugar_type_alias(ty_alias)?
    } else {
        (lift::lift_type_alias(genv, owner_id)?, lift::lift_refined_by(genv.tcx(), owner_id))
    };

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx(), owner_id, "fhir", &ty_alias).unwrap();
    }

    fhir.type_aliases.insert(def_id, genv.alloc(ty_alias));
    fhir.refined_by.insert(def_id, genv.alloc(refined_by));

    Ok(())
}

pub fn desugar_fn_sig<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    fn_sig: Option<&surface::FnSig>,
    resolver_output: &ResolverOutput,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let (fn_sig, opaque_tys) = if let Some(fn_sig) = fn_sig {
        let mut opaque_tys = Default::default();
        let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, Some(&mut opaque_tys));

        let fn_sig = cx.desugar_fn_sig(fn_sig)?;

        (fn_sig, opaque_tys)
    } else {
        lift::lift_fn(genv, owner_id)?
    };

    if config::dump_fhir() {
        dbg::dump_item_info(genv.tcx(), def_id, "fhir", fn_sig).unwrap();
    }

    fhir.fns.insert(def_id, genv.alloc(fn_sig));
    fhir.opaque_tys.extend_unord(opaque_tys.into_items());

    Ok(())
}

pub fn desugar_trait<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    resolver_output: &ResolverOutput,
    trait_: &surface::Trait,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let trait_ = cx.desugar_trait(trait_)?;

    fhir.traits.insert(def_id, genv.alloc(trait_));

    Ok(())
}

pub fn desugar_impl<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
    resolver_output: &ResolverOutput,
    impl_: &surface::Impl,
    fhir: &mut fhir::Crate<'genv>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = owner_id.def_id;

    let mut cx = RustItemCtxt::new(genv, owner_id, resolver_output, None);
    let impl_ = cx.desugar_impl(impl_)?;

    fhir.impls.insert(def_id, genv.alloc(impl_));

    Ok(())
}

pub fn desugar_sort_decl(sort_decl: &surface::SortDecl) -> fhir::SortDecl {
    fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span }
}
