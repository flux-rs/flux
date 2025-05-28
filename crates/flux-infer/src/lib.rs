#![feature(never_type, rustc_private, if_let_guard)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod evars;
pub mod fixpoint_encoding;
pub mod fixpoint_qualifiers;
pub mod infer;
pub mod lean_encoding;
pub mod lean_format;
pub mod projections;
pub mod refine_tree;
pub mod wkvars;
