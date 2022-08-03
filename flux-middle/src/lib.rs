#![feature(rustc_private, once_cell, if_let_guard, min_specialization, box_patterns)]

//! This crate contains common type definitions that are used by other crates.

extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;

pub mod core;
pub mod global_env;
mod intern;
pub mod pretty;
pub mod rustc;
pub mod ty;
