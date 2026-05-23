#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{Config, common::Mode};
use itertools::Itertools;
use tests::{FLUX_SYSROOT, default_flags};

#[derive(Debug)]
enum Suite {
    /// Run only `pos/` and `neg/` (tier-1, no sysroot libs needed).
    Basic,
    /// Run only `with_deps/pos/` and `with_deps/neg/` (tier-2, sysroot libs required).
    WithDeps,
}

impl Suite {
    fn post_tests(&self) -> PathBuf {
        match self {
            Suite::Basic => ["tests", "pos"].iter().collect(),
            Suite::WithDeps => ["tests", "with_deps", "pos"].iter().collect(),
        }
    }

    fn neg_tests(&self) -> PathBuf {
        match self {
            Suite::Basic => ["tests", "neg"].iter().collect(),
            Suite::WithDeps => ["tests", "with_deps", "neg"].iter().collect(),
        }
    }
}

#[derive(Debug)]
struct Args {
    filters: Vec<String>,
    flux: PathBuf,
    sysroot: PathBuf,
    /// Which subset of test suites to run.
    suite: Suite,
}

impl Args {
    fn parse() -> Args {
        let mut filters = vec![];
        let mut sysroot = None;
        let mut flux = None;
        let mut suite = None;
        for (arg, val) in env::args().tuple_windows() {
            match &arg[..] {
                "--filter" => filters.push(val.clone()),
                "--flux" => {
                    if flux.is_some() {
                        panic!("option '--flux' given more than once");
                    }
                    flux = Some(val.clone());
                }
                "--sysroot" => {
                    if sysroot.is_some() {
                        panic!("option '--sysroot' given more than once");
                    }
                    sysroot = Some(val.clone());
                }
                "--suite" => {
                    if suite.is_some() {
                        panic!("option '--suite' given more than once");
                    }
                    suite = Some(match val.as_str() {
                        "basic" => Suite::Basic,
                        "with-deps" => Suite::WithDeps,
                        other => {
                            panic!(
                                "unknown --suite value: `{other}`; expected `basic` or `with-deps`"
                            )
                        }
                    });
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
        let Some(suite) = suite else {
            panic!("option '--suite' must be provided");
        };
        Args { filters, flux: PathBuf::from(flux), sysroot: PathBuf::from(sysroot), suite }
    }
}

fn test_runner(_: &[&()]) {
    let args = Args::parse();
    let mut config = Config { rustc_path: args.flux, filters: args.filters, ..Config::default() };

    let mut flags = default_flags();

    // Pass `--emit=metadata` and `-Ffull-compilation=on` to make sure we emit `.fluxmeta` and
    // other artifacts for tests using `@aux-build`.
    flags.extend(["--emit=metadata".to_string(), "-Ffull-compilation=on".to_string()]);

    // Pass `-Fsummary=off` to disable printing the summary at the end of each test
    flags.extend(["-Fsummary=off".to_string()]);

    config.target_rustcflags = Some(flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

    // SAFETY: this is safe because this part of the code is single threaded
    unsafe {
        // Set the sysroot dir so the `flux` binary can find the correct `flux-driver.
        env::set_var(FLUX_SYSROOT, args.sysroot);
    }

    let path = args.suite.post_tests();
    if path.exists() {
        config.mode = Mode::Ui;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }

    let path = args.suite.neg_tests();
    if path.exists() {
        config.mode = Mode::CompileFail;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }
}
