#![feature(rustc_private)]

extern crate rustc_driver;

use std::{env, io, ops::Deref, process::exit};

use flux_config::{
    self as config,
    flags::{self, EXIT_FAILURE},
};
use flux_driver::callbacks::FluxCallbacks;
use rustc_driver::{catch_with_exit_code, run_compiler};

mod logger;

fn main() -> io::Result<()> {
    if !config::verify() {
        rustc_driver::install_ice_hook(rustc_driver::DEFAULT_BUG_REPORT_URL, |_| ());
        rustc_driver::main();
    }

    logger::install()?;

    // Remove all flux arguments
    let mut args: Vec<String> = env::args().filter(|arg| !flags::is_flux_arg(arg)).collect();

    // Report an error when passing `-C incremental=..` because that makes the borrow checker
    // to not run and we fail to retrieve the mir.
    let mut is_codegen = false;
    for arg in &args {
        if arg.starts_with("-C") || arg.starts_with("--codegen") {
            is_codegen = true;
        } else {
            if is_codegen && arg.starts_with("incremental=") {
                eprintln!("error: `flux-driver` cannot be called with `-C incremental=val`\n");
                std::process::exit(EXIT_FAILURE);
            }
            is_codegen = false;
        }
    }

    args.push("--sysroot".into());
    args.push(sysroot().expect("Flux Rust requires rustup to be built."));
    args.push("-Coverflow-checks=off".to_string());
    args.push("-Zcrate-attr=feature(register_tool, custom_inner_attributes)".to_string());
    args.push("-Zcrate-attr=register_tool(flux)".to_string());
    args.push("-Zcrate-attr=register_tool(flux_tool)".to_string());
    args.push("--cfg=flux".to_string());

    let exit_code = catch_with_exit_code(move || {
        run_compiler(&args, &mut FluxCallbacks);
    });
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
