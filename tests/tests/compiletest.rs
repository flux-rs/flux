#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{common::Mode, Config};
use itertools::Itertools;
use tests::{default_rustc_flags, find_flux_path, FLUX_FULL_COMPILATION, FLUX_SYSROOT};

fn config() -> Config {
    let bless = env::args().any(|arg| arg == "--bless");
    let filters = env::args()
        .tuple_windows()
        .filter_map(|(arg, val)| if arg == "--test-args" { Some(val) } else { None })
        .collect_vec();
    Config { rustc_path: find_flux_path(), filters, bless, ..Config::default() }
}

fn test_runner(_: &[&()]) {
    let mut config = config().tempdir();

    let mut rustc_flags = default_rustc_flags();

    // Pass `--emit=metadata` to make sure we emit a `.fluxmeta` file
    rustc_flags.extend(["--emit=metadata".to_string()]);

    config.target_rustcflags = Some(rustc_flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

    // Force full compilation to make sure we generate artifacts when annotating tests with `@aux-build`
    env::set_var(FLUX_FULL_COMPILATION, "1");
    env::set_var(FLUX_SYSROOT, config.rustc_path.parent().unwrap());

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
