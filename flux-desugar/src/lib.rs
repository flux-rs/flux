#![feature(rustc_private)]
#![feature(min_specialization)]
#![feature(box_patterns, once_cell)]

extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod desugar;
mod table_resolver;
mod zip_resolver;

use flux_errors::FluxSession;
use flux_middle::{
    core::{self, AdtSortsMap},
    global_env::ConstInfo,
    rustc,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub use desugar::{desugar_enum_def, desugar_qualifier, resolve_sorts};
use rustc_span::Span;

pub fn desugar_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    consts: &[ConstInfo],
    struct_def: surface::StructDef,
) -> Result<core::StructDef, ErrorGuaranteed> {
    let mut resolver = table_resolver::Resolver::from_adt(tcx, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;
    desugar::desugar_struct_def(tcx, sess, consts, struct_def)
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

pub fn desugar_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    consts: &[ConstInfo],
    sorts: &impl AdtSortsMap,
    def_id: DefId,
    fn_sig: surface::FnSig,
) -> Result<core::FnSig, ErrorGuaranteed> {
    let rust_sig = rustc::lowering::lower_fn_sig(tcx, tcx.fn_sig(def_id))?;
    let sig = zip_resolver::zip_bare_def(tcx, fn_sig, &rust_sig);
    desugar::desugar_fn_sig(sess, sorts, consts, sig)
}
