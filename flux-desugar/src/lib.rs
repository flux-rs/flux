#![feature(rustc_private)]
#![feature(min_specialization)]
#![feature(box_patterns, once_cell)]
#![feature(let_chains)]

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

pub use desugar::{
    desugar_adt_def, desugar_defn, desugar_qualifier, resolve_defn_uif, resolve_uif_def,
};
use flux_errors::FluxSession;
use flux_middle::fhir;
use flux_syntax::surface::{self, TyCtxt};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::LocalDefId;

pub fn desugar_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    struct_def: surface::StructDef,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(tcx, sess, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;

    // Check
    annot_check::check_struct_def(tcx, sess, &struct_def)?;

    // Desugar
    desugar::desugar_struct_def(tcx, sess, map, struct_def)
}

pub fn desugar_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    enum_def: surface::EnumDef,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(tcx, sess, enum_def.def_id)?;
    let enum_def = resolver.resolve_enum_def(enum_def)?;

    // Check
    annot_check::check_enum_def(tcx, sess, &enum_def)?;

    // Desugar
    desugar::desugar_enum_def(tcx, sess, map, enum_def)
}

pub fn desugar_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    def_id: LocalDefId,
    fn_sig: surface::FnSig,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    // Resolve
    let resolver = table_resolver::Resolver::new(tcx, sess, def_id)?;
    let fn_sig = resolver.resolve_fn_sig(fn_sig)?;

    // Check
    annot_check::check_fn_sig(tcx, sess, def_id.to_def_id(), &fn_sig)?;

    // Desugar
    desugar::desugar_fn_sig(tcx, sess, map, fn_sig)
}
