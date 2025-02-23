#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{Config, common::Mode};
use itertools::Itertools;
use tests::{FLUX_FULL_COMPILATION, FLUX_SYSROOT, default_rustc_flags};

#[derive(Debug)]
struct Args {
    filters: Vec<String>,
    flux: PathBuf,
    sysroot: PathBuf,
}

impl Args {
    fn parse() -> Args {
        let mut filters = vec![];
        let mut sysroot = None;
        let mut flux = None;
        for (arg, val) in env::args().tuple_windows() {
            match &arg[..] {
                "--filter" => {
                    filters.push(val);
                }
                "--flux" => {
                    if flux.is_some() {
                        panic!("option '--flux' given more than once");
                    }
                    flux = Some(val);
                }
                "--sysroot" => {
                    if sysroot.is_some() {
                        panic!("option '--sysroot' given more than once");
                    }
                    sysroot = Some(val);
                }
                _ => {}
            }
        }
        let Some(flux) = flux else {
            panic!("option '--flux' must be provided");
        };
        let Some(sysroot) = sysroot else {
            panic!("option '--sysroot' must be provided");
        };
        Args { filters, flux: PathBuf::from(flux), sysroot: PathBuf::from(sysroot) }
    }
}

fn test_runner(_: &[&()]) {
    let args = Args::parse();
    let mut config = Config { rustc_path: args.flux, filters: args.filters, ..Config::default() };

    let mut rustc_flags = default_rustc_flags();

    // Pass `--emit=metadata` to make sure we emit a `.fluxmeta` file
    rustc_flags.extend(["--emit=metadata".to_string()]);

    config.target_rustcflags = Some(rustc_flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

    // SAFETY: this is safe because this part of the code is single threaded
    unsafe {
        // Force full compilation to make sure we generate artifacts when annotating tests with `@aux-build`
        env::set_var(FLUX_FULL_COMPILATION, "1");
        env::set_var(FLUX_SYSROOT, &args.sysroot);
    }

    let path: PathBuf = ["tests", "pos"].iter().collect();
    if path.exists() {
        config.mode = Mode::Ui;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }

    let path: PathBuf = ["tests", "neg"].iter().collect();
    if path.exists() {
        config.mode = Mode::CompileFail;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }
}
