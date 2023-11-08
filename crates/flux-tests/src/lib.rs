#![feature(register_tool)]
use std::path::PathBuf;

// CODESYNC(sysroot-env) we must use the same env var in flux-bin
pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

pub fn find_flux_path() -> PathBuf {
    let executable_name = if cfg!(windows) { "rustc-flux.exe" } else { "rustc-flux" };
    find_file_in_target_dir(executable_name)
}

/// Rustc flags to pass Flux when running tests
pub fn rustc_flags() -> Vec<String> {
    vec!["--crate-type=rlib".to_string(), "--edition=2021".to_string()]
}

fn find_file_in_target_dir(file: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) { "debug" } else { "release" };
    let local_path: PathBuf = ["target", target_directory, file].into_iter().collect();
    if local_path.exists() {
        return local_path;
    }
    let workspace_path: PathBuf = ["..", "..", "target", target_directory, file]
        .into_iter()
        .collect();
    if workspace_path.exists() {
        return workspace_path;
    }
    panic!("Could not find {file}");
}
