#![feature(rustc_private)]

extern crate rustc_driver;

use std::{env, io, process::exit};

use flux_driver::callbacks::FluxCallbacks;
use rustc_driver::{catch_with_exit_code, RunCompiler};

mod logger;

fn main() -> io::Result<()> {
    let resolve_logs = logger::install()?;

    // CODESYNC(flux-cargo) Check if we are being called from cargo.
    let in_cargo = env::var("FLUX_CARGO").is_ok();

    // HACK(nilehmann)
    // Disable incremental compilation because that makes the borrow checker to not run
    // and we fail to retrieve the mir.
    let mut args = vec![];
    let mut is_codegen = false;
    for arg in env::args() {
        if arg.starts_with("-C") || arg.starts_with("--codegen") {
            is_codegen = true;
        } else if is_codegen && arg.starts_with("incremental=") {
            is_codegen = false;
        } else {
            if is_codegen {
                args.push("-C".to_string());
                is_codegen = false;
            }
            args.push(arg);
        }
    }
    // Add the sysroot path to the arguments.
    args.push("--sysroot".into());
    args.push(sysroot().expect("Flux Rust requires rustup to be built."));
    args.push("-Coverflow-checks=off".to_string());

    let exit_code = run_compiler(args, in_cargo);
    resolve_logs()?;
    exit(exit_code)
}

/// Get the path to the sysroot of the current rustup toolchain. Return `None` if the rustup
/// environment variables are not set.
fn sysroot() -> Option<String> {
    let home = option_env!("RUSTUP_HOME")?;
    let toolchain = option_env!("RUSTUP_TOOLCHAIN")?;
    Some(format!("{home}/toolchains/{toolchain}"))
}

/// Run Flux Rust and return the exit status code.
pub fn run_compiler(args: Vec<String>, in_cargo: bool) -> i32 {
    // HACK(nilehmann) When running flux we want to stop compilation after analysis
    // to avoid creating a binary. However, stopping compilation messes up with cargo so we
    // pass full_compilation=true if we detect we are being called from cargo
    let mut callbacks = FluxCallbacks::new(in_cargo);
    catch_with_exit_code(move || RunCompiler::new(&args, &mut callbacks).run())
}
