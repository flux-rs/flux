#![feature(rustc_private)]

extern crate rustc_driver;

use std::{env, io, process::ExitCode};

use flux_config::{
    self as config,
    flags::{self, EXIT_FAILURE},
};
use flux_driver::callbacks::FluxCallbacks;
use flux_middle::metrics;
use rustc_driver::{catch_fatal_errors, run_compiler};

mod logger;

fn main() -> ExitCode {
    if !config::verify() {
        return rustc_driver::main();
    }

    match run() {
        Ok(exit_code) => exit_code,
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> io::Result<ExitCode> {
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

    args.push("-Coverflow-checks=off".to_string());
    args.push("-Zcrate-attr=feature(register_tool, custom_inner_attributes)".to_string());
    args.push("-Zcrate-attr=register_tool(flux)".to_string());
    args.push("-Zcrate-attr=register_tool(flux_tool)".to_string());
    args.push("--cfg=flux".to_string());

    let start = std::time::Instant::now();
    let result = catch_fatal_errors(move || {
        run_compiler(&args, &mut FluxCallbacks);
    });
    if config::summary() && result.is_ok() {
        metrics::print_summary(start.elapsed())?;
    };
    #[cfg(feature = "suggestions")]
    metrics::print_suggestion_comparison_summary()?;
    Ok(if result.is_ok() { ExitCode::SUCCESS } else { ExitCode::FAILURE })
}
