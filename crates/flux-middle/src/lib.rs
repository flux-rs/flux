#![warn(unused_extern_crates)]
#![feature(
    associated_type_defaults,
    box_patterns,
    if_let_guard,
    lazy_cell,
    let_chains,
    min_specialization,
    never_type,
    rustc_private,
    unwrap_infallible
)]

//! This crate contains common type definitions that are used by other crates.

extern crate elsa;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

pub mod const_eval;
pub mod cstore;
pub mod fhir;
pub mod global_env;
pub mod intern;
pub mod pretty;
pub mod queries;
pub mod rty;
pub mod rustc;

use flux_macros::fluent_messages;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }
