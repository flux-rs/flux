#![feature(rustc_private)]
#![feature(min_specialization)]

extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_serialize;
extern crate rustc_span;

pub mod mir;
pub mod ty;
