#![feature(rustc_private, box_patterns, once_cell)]

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
mod resolve;

use callbacks::LiquidCallbacks;
use rustc_driver::{catch_with_exit_code, RunCompiler};

/// Get the path to the sysroot of the current rustup toolchain. Return `None` if the rustup
/// environment variables are not set.
fn sysroot() -> Option<String> {
    let home = option_env!("RUSTUP_HOME")?;
    let toolchain = option_env!("RUSTUP_TOOLCHAIN")?;
    Some(format!("{}/toolchains/{}", home, toolchain))
}

pub fn run_compiler_result(mut args: Vec<String>) -> Result<liquid_rust_fixpoint::FixpointResult, rustc_errors::ErrorReported> {
    println!("Here come the raw args {:?}", args);
    // Add the sysroot path to the arguments.
    args.push("--sysroot".into());
    args.push(sysroot().expect("Liquid Rust requires rustup to be built."));
    // Add release mode to the arguments.
    args.push("-O".into());
    // We don't support unwinding.
    args.push("-Cpanic=abort".into());
    // Run the rust compiler with the arguments.
    let mut callbacks = LiquidCallbacks::default();
    let res = RunCompiler::new(&args, &mut callbacks).run();
    println!("RUN COMPILER: args = {:?}, result = {:?}", args, callbacks.result);
    match res {
        Ok(_) => Ok(callbacks.result),
        Err(e) => Err(e),
    }
}

/// Run Liquid Rust and return the exit status code.
pub fn run_compiler(args: Vec<String>) -> i32 {
    catch_with_exit_code(move || match run_compiler_result(args) { 
        Ok(_) => Ok(()),
        Err(e) => Err(e),
    })
}


