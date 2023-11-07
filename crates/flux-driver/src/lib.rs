#![feature(rustc_private, box_patterns, let_chains)]

extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

pub mod callbacks;
mod collector;

use flux_macros::fluent_messages;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

pub static DEFAULT_LOCALE_RESOURCES: &[&str] = &[
    DEFAULT_LOCALE_RESOURCE,
    flux_desugar::DEFAULT_LOCALE_RESOURCE,
    flux_fhir_analysis::DEFAULT_LOCALE_RESOURCE,
    flux_metadata::DEFAULT_LOCALE_RESOURCE,
    flux_middle::DEFAULT_LOCALE_RESOURCE,
    flux_refineck::DEFAULT_LOCALE_RESOURCE,
];
