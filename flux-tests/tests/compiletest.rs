#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{common::Mode, Config};
use itertools::Itertools;

fn find_flux_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) { "debug" } else { "release" };
    let executable_name = if cfg!(windows) { "flux.exe" } else { "flux" };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {:?} flux binary to be used in tests. \
        It might be that flux has not been compiled correctly.",
        target_directory
    );
}

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

    config.target_rustcflags = Some("--crate-type=rlib".to_string());

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
