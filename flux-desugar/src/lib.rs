#![feature(rustc_private)]
#![feature(min_specialization)]
#![feature(box_patterns, once_cell)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod annot_check;
mod desugar;
mod table_resolver;

pub use desugar::{desugar_adt_def, desugar_qualifier, resolve_sorts, resolve_uif_def};
use flux_middle::{fhir, global_env::GlobalEnv};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::LocalDefId;

pub fn desugar_struct_def(
    genv: &GlobalEnv,
    struct_def: surface::StructDef,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(genv, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;

    // Check
    annot_check::check_struct_def(genv.tcx, genv.sess, &struct_def)?;

    // Desugar
    desugar::desugar_struct_def(genv.sess, genv.map(), struct_def)
}

pub fn desugar_enum_def(
    genv: &GlobalEnv,
    enum_def: surface::EnumDef,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(genv, enum_def.def_id)?;
    let enum_def = resolver.resolve_enum_def(enum_def)?;

    // Check
    annot_check::check_enum_def(genv.tcx, genv.sess, &enum_def)?;

    // Desugar
    desugar::desugar_enum_def(genv.sess, genv.map(), enum_def)
}

pub fn desugar_fn_sig(
    genv: &GlobalEnv,
    def_id: LocalDefId,
    fn_sig: surface::FnSig,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(genv, def_id)?;
    let fn_sig = resolver.resolve_fn_sig(fn_sig)?;

    // Check
    annot_check::check_fn_sig(genv.tcx, genv.sess, def_id.to_def_id(), &fn_sig)?;

    // Desugar
    desugar::desugar_fn_sig(genv.sess, genv.map(), fn_sig)
}
