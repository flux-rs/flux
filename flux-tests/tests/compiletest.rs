#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf};

use compiletest_rs::{common::Mode, Config};
use itertools::Itertools;

fn find_file_in_target_dir(file: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) { "debug" } else { "release" };
    let local_flux_driver_path: PathBuf = ["target", target_directory, file].into_iter().collect();
    if local_flux_driver_path.exists() {
        return local_flux_driver_path;
    }
    let workspace_flux_driver_path: PathBuf = ["..", "target", target_directory, file]
        .into_iter()
        .collect();
    if workspace_flux_driver_path.exists() {
        return workspace_flux_driver_path;
    }
    panic!("Could not find {file}");
}

fn find_flux_path() -> PathBuf {
    let executable_name = if cfg!(windows) { "flux-driver.exe" } else { "flux-driver" };
    find_file_in_target_dir(executable_name)
}

fn find_attrs_proc_macro_lib_path() -> PathBuf {
    let attrs_proc_macros_lib = if cfg!(target_os = "linux") {
        "libflux_attrs_proc_macros.so"
    } else {
        todo!("implement this for mac and windows")
    };
    find_file_in_target_dir(attrs_proc_macros_lib)
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

    config.target_rustcflags = Some(format!(
        "--crate-type=rlib --extern flux_attrs_proc_macros={} --edition=2018",
        find_attrs_proc_macro_lib_path().display()
    ));

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
