#![feature(rustc_private)]
#![feature(const_panic)]

extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_serialize;
extern crate rustc_span;

pub mod mir;
pub mod ty;
