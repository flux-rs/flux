#![feature(rustc_private, box_patterns)]

extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

pub mod callbacks;
mod collector;

use flux_macros::fluent_messages;

fluent_messages! { "../locales/en-US.ftl" }
