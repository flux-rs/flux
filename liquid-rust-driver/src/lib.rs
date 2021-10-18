#![feature(rustc_private, box_patterns)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod callbacks;
mod collector;
mod lowering;
mod wf;

use callbacks::LiquidCallbacks;
use rustc_driver::{catch_with_exit_code, RunCompiler};

/// Run Liquid Rust and return the exit status code.
pub fn run_compiler(args: Vec<String>) -> i32 {
    let mut callbacks = LiquidCallbacks::default();

    catch_with_exit_code(move || RunCompiler::new(&args, &mut callbacks).run())
}
