#![feature(rustc_private, let_chains, box_patterns)]

// extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
// extern crate rustc_index;
// extern crate rustc_middle;
// extern crate rustc_serialize;
// extern crate rustc_session;
extern crate rustc_span;

use flux_macros::fluent_messages;
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

pub mod annot_check;
pub mod wf;
