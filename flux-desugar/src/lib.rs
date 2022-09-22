#![feature(rustc_private)]
#![feature(min_specialization)]
#![feature(box_patterns, once_cell, let_else)]

extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod desugar;
mod table_resolver;
mod zip_resolver;

pub use desugar::{desugar_qualifier, resolve_sorts};
use flux_middle::{
    core::{self, AdtSortsMap},
    global_env::GlobalEnv,
    rustc,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

pub fn desugar_struct_def(
    genv: &GlobalEnv,
    struct_def: surface::StructDef,
) -> Result<core::StructDef, ErrorGuaranteed> {
    let resolver = table_resolver::Resolver::from_adt(genv, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;
    desugar::desugar_struct_def(genv.sess, &genv.consts, struct_def)
}

pub fn desugar_enum_def(
    genv: &GlobalEnv,
    adt_sorts: &impl AdtSortsMap,
    enum_def: surface::EnumDef,
) -> Result<core::EnumDef, ErrorGuaranteed> {
    let def_id = enum_def.def_id;
    let rust_adt_def = genv.tcx.adt_def(def_id.to_def_id());
    let resolver = table_resolver::Resolver::from_adt(genv, def_id)?;
    let rust_enum_def = rustc::lowering::lower_enum_def(genv.tcx, rust_adt_def)?;
    let enum_def = zip_resolver::ZipResolver::new(genv.tcx, genv.sess, &resolver)
        .zip_enum_def(enum_def, &rust_enum_def)?;
    desugar::desugar_enum_def(genv.sess, &genv.consts, adt_sorts, enum_def)
}

pub fn desugar_fn_sig(
    genv: &GlobalEnv,
    sorts: &impl AdtSortsMap,
    def_id: DefId,
    fn_sig: surface::FnSig,
) -> Result<core::FnSig, ErrorGuaranteed> {
    let rust_fn_sig = genv.tcx.fn_sig(def_id);
    let resolver = table_resolver::Resolver::from_rust_fn_sig(genv, rust_fn_sig)?;
    let rust_sig = rustc::lowering::lower_fn_sig(genv.tcx, rust_fn_sig)?;
    let sig = zip_resolver::ZipResolver::new(genv.tcx, genv.sess, &resolver)
        .zip_fn_sig(fn_sig, &rust_sig)?;
    desugar::desugar_fn_sig(genv.sess, sorts, &genv.consts, sig)
}

// TODO(RJ): This is not used but perhaps *could* used to generate default
// type signatures for const (instead of the current "inline" method?)
pub fn const_ty(
    rust_ty: &flux_middle::rustc::ty::Ty,
    val: i128,
    span: Span,
) -> flux_middle::core::Ty {
    let bty = match rust_ty.kind() {
        rustc::ty::TyKind::Int(i) => core::BaseTy::Int(*i),
        rustc::ty::TyKind::Uint(u) => core::BaseTy::Uint(*u),
        kind => panic!("const_ty: cannot handle {kind:?}"),
    };

    let expr = core::Expr::from_i128(val);
    let idx = core::Index { expr, is_binder: false };
    let indices = core::Indices { indices: vec![idx], span };
    core::Ty::Indexed(bty, indices)
}
