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

mod desugar;
mod table_resolver;
mod zip_checker;
// mod zip_resolver;

pub use desugar::{desugar_adt_def, desugar_qualifier, resolve_sorts, resolve_uif_def};
use flux_errors::ResultExt;
use flux_middle::{
    fhir::{self, AdtMap},
    global_env::GlobalEnv,
    rustc::{self, lowering},
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::LocalDefId;
use rustc_span::Span;

pub fn desugar_struct_def(
    genv: &GlobalEnv,
    adt_sorts: &AdtMap,
    struct_def: surface::StructDef,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::new(genv, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;
    desugar::desugar_struct_def(genv.sess, &genv.consts, adt_sorts, struct_def)
}

pub fn desugar_enum_def(
    genv: &GlobalEnv,
    adt_sorts: &AdtMap,
    enum_def: surface::EnumDef,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    let def_id = enum_def.def_id;

    let resolver = table_resolver::Resolver::new(genv, def_id)?;
    let enum_def = resolver.resolve_enum_def(enum_def)?;

    let rust_enum_def =
        lowering::lower_enum_def(genv.tcx, genv.sess, genv.tcx.adt_def(def_id.to_def_id()))?;
    zip_checker::ZipChecker::new(genv.tcx, genv.sess).zip_enum_def(&enum_def, &rust_enum_def)?;

    desugar::desugar_enum_def(genv.sess, &genv.consts, adt_sorts, enum_def)
}

pub fn desugar_fn_sig(
    genv: &GlobalEnv,
    sorts: &AdtMap,
    def_id: LocalDefId,
    fn_sig: surface::FnSig,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::new(genv, def_id)?;
    let sig = resolver.resolve_fn_sig(fn_sig)?;

    let rust_sig = lowering::lower_fn_sig_of(genv.tcx, def_id.to_def_id()).emit(genv.sess)?;
    zip_checker::ZipChecker::new(genv.tcx, genv.sess).zip_fn_sig(&sig, &rust_sig)?;

    desugar::desugar_fn_sig(genv.sess, sorts, &genv.consts, sig)
}

// TODO(RJ): This is not used but perhaps *could* used to generate default
// type signatures for const (instead of the current "inline" method?)
pub fn const_ty(
    rust_ty: &flux_middle::rustc::ty::Ty,
    val: i128,
    span: Span,
) -> flux_middle::fhir::Ty {
    let bty = match rust_ty.kind() {
        rustc::ty::TyKind::Int(i) => fhir::BaseTy::Int(*i),
        rustc::ty::TyKind::Uint(u) => fhir::BaseTy::Uint(*u),
        kind => panic!("const_ty: cannot handle {kind:?}"),
    };

    let expr = fhir::Expr::from_i128(val);
    let idx = fhir::Index { expr, is_binder: false };
    let indices = fhir::Indices { indices: vec![idx], span };
    fhir::Ty::Indexed(bty, indices)
}
