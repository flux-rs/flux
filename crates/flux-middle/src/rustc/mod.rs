//! This module contains simplified versions of some structures in rustc. The definitions
//! in this module can be understood as the current supported subset of rust. As we implement
//! more features we should be able to work directly on rustc's structures.

use rustc_middle::ty::TyCtxt;

pub mod mir;
pub mod ty;

pub mod lowering;

pub trait ToRustc<'tcx> {
    type T;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T;
}
