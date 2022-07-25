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
    core::{self, AdtSortsMap, ConstSig},
    global_env::ConstInfo,
    rustc,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    definitions::DefPathData,
};
use rustc_middle::ty::{ScalarInt, TyCtxt};

pub use desugar::{desugar_enum_def, desugar_qualifier, resolve_sorts};
use rustc_span::{Span, Symbol};

pub fn desugar_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    consts: &Vec<ConstInfo>,
    struct_def: surface::StructDef,
) -> Result<core::StructDef, ErrorGuaranteed> {
    let mut resolver = table_resolver::Resolver::from_adt(tcx, struct_def.def_id)?;
    let struct_def = resolver.resolve_struct_def(struct_def)?;
    desugar::desugar_struct_def(tcx, sess, consts, struct_def)
}

pub fn desugar_const_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
    const_sig: surface::ConstSig,
    val: rustc_middle::ty::ScalarInt,
) -> Result<core::ConstSig, ErrorGuaranteed> {
    let rust_ty = rustc::lowering::lower_ty(tcx, tcx.type_of(def_id))?;
    let ty = match const_sig.ty {
        Some(ty) => {
            let ty = zip_resolver::zip_ty(ty, &rust_ty);
            desugar::desugar_ty(sess, &vec![], ty)?
        }
        None => const_ty(&rust_ty, val, const_sig.span),
    };
    let sym = def_id_symbol(tcx, def_id);
    Ok(ConstSig { sym, val, ty })
}

pub fn const_ty(
    rust_ty: &flux_middle::rustc::ty::Ty,
    val: ScalarInt,
    span: Span,
) -> flux_middle::core::Ty {
    let bty = match rust_ty.kind() {
        rustc::ty::TyKind::Int(i) => core::BaseTy::Int(*i),
        rustc::ty::TyKind::Uint(u) => core::BaseTy::Uint(*u),
        kind => panic!("const_ty: cannot handle {kind:?}"),
    };
    let size = val.size();
    let expr = if let Ok(v) = val.try_to_int(size) {
        core::Expr::from_i128(v)
    } else {
        panic!("const_expr: cannot convert {val:?}");
    };
    let idx = core::Index { expr, is_binder: false };
    let indices = core::Indices { indices: vec![idx], span };
    core::Ty::Indexed(bty, indices)
}

fn def_id_symbol(tcx: TyCtxt, def_id: LocalDefId) -> Symbol {
    let did = def_id.to_def_id();
    let def_path = tcx.def_path(did);
    if let Some(dp) = def_path.data.last() {
        if let DefPathData::ValueNs(sym) = dp.data {
            println!("def_id_symbol {def_id:?} with {sym:?}");
            return sym;
        }
    }
    panic!("def_id_symbol fails on {did:?}")
}

pub fn desugar_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    consts: &Vec<ConstInfo>,
    sorts: &impl AdtSortsMap,
    def_id: DefId,
    fn_sig: surface::FnSig,
) -> Result<core::FnSig, ErrorGuaranteed> {
    let rust_sig = rustc::lowering::lower_fn_sig(tcx, tcx.fn_sig(def_id))?;
    let sig = zip_resolver::zip_bare_def(fn_sig, &rust_sig);
    desugar::desugar_fn_sig(sess, sorts, consts, sig)
}
