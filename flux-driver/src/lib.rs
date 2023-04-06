#![warn(unused_extern_crates)]
#![feature(rustc_private, box_patterns, let_chains)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_borrowck;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod callbacks;
mod collector;

use callbacks::FluxCallbacks;
use flux_macros::fluent_messages;
use rustc_driver::{catch_with_exit_code, RunCompiler};
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

/// Get the path to the sysroot of the current rustup toolchain. Return `None` if the rustup
/// environment variables are not set.
fn sysroot() -> Option<String> {
    let home = option_env!("RUSTUP_HOME")?;
    let toolchain = option_env!("RUSTUP_TOOLCHAIN")?;
    Some(format!("{home}/toolchains/{toolchain}"))
}

/// Run Flux Rust and return the exit status code.
pub fn run_compiler(mut args: Vec<String>, in_cargo: bool) -> i32 {
    // Add the sysroot path to the arguments.
    args.push("--sysroot".into());
    args.push(sysroot().expect("Flux Rust requires rustup to be built."));
    // Add release mode to the arguments.
    args.push("-O".into());
    // HACK(nilehmann) When running flux we want to stop compilation after analysis
    // to avoid creating a binary. However, stopping compilation messes up with cargo so we
    // pass full_compilation=true if we detect we are being called from cargo
    let mut callbacks = FluxCallbacks::new(in_cargo);
    catch_with_exit_code(move || RunCompiler::new(&args, &mut callbacks).run())
}
