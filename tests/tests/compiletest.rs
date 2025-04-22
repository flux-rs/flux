#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{Config, common::Mode};
use itertools::Itertools;
use tests::default_flags;

#[derive(Debug)]
struct Args {
    filters: Vec<String>,
    flux: PathBuf,
}

impl Args {
    fn parse() -> Args {
        let mut filters = vec![];
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
                _ => {}
            }
        }
        let Some(flux) = flux else {
            panic!("option '--flux' must be provided");
        };
        Args { filters, flux: PathBuf::from(flux) }
    }
}

fn test_runner(_: &[&()]) {
    let args = Args::parse();
    let mut config = Config { rustc_path: args.flux, filters: args.filters, ..Config::default() };

    let mut flags = default_flags();

    // Pass `--emit=metadata` and `-Ffull-compilation=on` to make sure we emit `.fluxmeta` and
    // other artifacts for tests using `@aux-build`.
    flags.extend(["--emit=metadata".to_string(), "-Ffull-compilation=on".to_string()]);

    config.target_rustcflags = Some(flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

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
