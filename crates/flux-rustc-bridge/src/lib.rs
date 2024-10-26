//! This crate contains simplified versions of some structures in rustc. The definitions
//! in this module can be understood as the current supported subset of rust. As we implement
//! more features we should be able to work directly on rustc's structures.

#![feature(rustc_private, box_patterns, associated_type_defaults, never_type)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

use flux_macros::fluent_messages;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

fluent_messages! { "../locales/en-US.ftl" }

pub mod const_eval;
pub mod lowering;
pub mod mir;
pub mod ty;

pub trait ToRustc<'tcx> {
    type T;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T;
}

impl<'tcx> ToRustc<'tcx> for rustc_middle::ty::Ty<'tcx> {
    type T = Self;

    fn to_rustc(&self, _tcx: TyCtxt<'tcx>) -> Self {
        *self
    }
}

pub fn def_id_to_string(def_id: DefId) -> String {
    rustc_middle::ty::tls::with(|tcx| tcx.def_path_str(def_id))
}

pub fn def_id_to_parent_span(def_id: DefId) -> rustc_span::Span {
    rustc_middle::ty::tls::with(|tcx| tcx.def_span(def_id))
}
