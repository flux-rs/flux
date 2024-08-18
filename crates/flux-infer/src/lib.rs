#![feature(extract_if, let_chains, never_type, rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_type_ir;

pub mod fixpoint_encoding;
pub mod infer;
pub mod refine_tree;
