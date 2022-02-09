#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]
use std::{env, path::PathBuf};

use compiletest_rs::{common::Mode, Config};

fn find_liquid_rust_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "liquid-rust.exe"
    } else {
        "liquid-rust"
    };
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
        "Could not find the {:?} liquid-rust binary to be used in tests. \
        It might be that liquid-rust has not been compiled correctly.",
        target_directory
    );
}

fn config() -> Config {
    let bless = env::args().any(|arg| arg == "--bless");
    Config {
        rustc_path: find_liquid_rust_path(),
        mode: Mode::Ui,
        bless,
        ..Config::default()
    }
}

fn test_runner(_: &[&()]) {
    let mut config = config();

    // // Filter the tests to run
    // if let Some(filter) = filter {
    //     config.filters.push(filter.clone());
    // }

    config.target_rustcflags = Some("--color=never --crate-type=rlib".to_string());

    let path: PathBuf = ["tests", "pos"].iter().collect();
    if path.exists() {
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }

    let path: PathBuf = ["tests", "fail"].iter().collect();
    if path.exists() {
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }
}
