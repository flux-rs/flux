#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{common::Mode, Config};
use flux_tests::{find_flux_path, rustc_flags};
use itertools::Itertools;

fn config() -> Config {
    let bless = env::args().any(|arg| arg == "--bless");
    let filters = env::args()
        .tuple_windows()
        .filter_map(|(arg, val)| if arg == "--test-args" { Some(val) } else { None })
        .collect_vec();
    Config { rustc_path: find_flux_path(), filters, bless, ..Config::default() }
}

fn test_runner(_: &[&()]) {
    let mut config = config();

    config.target_rustcflags = Some(rustc_flags().join(" "));

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
    config.clean_rmeta();
}
