#![feature(rustc_private)]

extern crate rustc_driver;

use std::{env, io, ops::Deref, process::exit};

use flux_driver::callbacks::FluxCallbacks;
use rustc_driver::{catch_with_exit_code, RunCompiler};

mod logger;

fn main() -> io::Result<()> {
    let resolve_logs = logger::install()?;

    // CODESYNC(flux-cargo) Check if we are being called from cargo.
    let in_cargo = env::var("FLUX_CARGO").is_ok();
    let primary_package = env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    // TODO(nilehmann): we should also run flux on dependencies with flux annotations to produce metadata.
    // The idea is to opt in to that in the metadata table of the Cargo.toml. Something like
    // ```
    // [package.metadata.flux]
    // export = true
    // ```
    // If we are being called from cargo but this is not the primary package, then we just call rustc.
    if in_cargo && !primary_package {
        rustc_driver::main();
    }

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

    args.push("--sysroot".into());
    args.push(sysroot().expect("Flux Rust requires rustup to be built."));
    args.push("-Coverflow-checks=off".to_string());
    args.push("-Zcrate-attr=feature(register_tool, custom_inner_attributes)".to_string());
    args.push("-Zcrate-attr=register_tool(flux)".to_string());
    args.push("-Zcrate-attr=register_tool(flux_tool)".to_string());
    args.push("--cfg=flux".to_string());

    let exit_code = catch_with_exit_code(move || RunCompiler::new(&args, &mut FluxCallbacks).run());
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

/// If a command-line option matches `find_arg`, then apply the predicate `pred` on its value. If
/// true, then return it. The parameter is assumed to be either `--arg=value` or `--arg value`.
pub fn arg_value<'a, T: Deref<Target = str>>(
    args: &'a [T],
    find_arg: &str,
    pred: impl Fn(&str) -> bool,
) -> Option<&'a str> {
    let mut args = args.iter().map(Deref::deref);
    while let Some(arg) = args.next() {
        let mut arg = arg.splitn(2, '=');
        if arg.next() != Some(find_arg) {
            continue;
        }

        match arg.next().or_else(|| args.next()) {
            Some(v) if pred(v) => return Some(v),
            _ => {}
        }
    }
    None
}
