use std::path::PathBuf;

pub fn find_flux_path() -> PathBuf {
    let executable_name = if cfg!(windows) { "flux-driver.exe" } else { "flux-driver" };
    find_file_in_target_dir(executable_name)
}

pub fn rustc_flags() -> Vec<String> {
    vec![
        "--crate-type=rlib".to_string(),
        "--edition=2021".to_string(),
        format!("--extern=flux_rs={}", find_flux_rs_lib_path().display()),
    ]
}

fn find_flux_rs_lib_path() -> PathBuf {
    let flux_rs_lib = if cfg!(target_os = "linux") {
        "libflux_rs.so"
    } else if cfg!(target_os = "macos") {
        "libflux_rs.dylib"
    } else {
        todo!("implement for windows")
    };
    find_file_in_target_dir(flux_rs_lib)
}

fn find_file_in_target_dir(file: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) { "debug" } else { "release" };
    let local_flux_driver_path: PathBuf = ["target", target_directory, file].into_iter().collect();
    if local_flux_driver_path.exists() {
        return local_flux_driver_path;
    }
    let workspace_flux_driver_path: PathBuf = ["..", "..", "target", target_directory, file]
        .into_iter()
        .collect();
    if workspace_flux_driver_path.exists() {
        return workspace_flux_driver_path;
    }
    panic!("Could not find {file}");
}
