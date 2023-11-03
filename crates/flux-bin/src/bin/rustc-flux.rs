use std::{
    env,
    process::{exit, Command},
};

use anyhow::Result;
use flux_bin::utils::{
    get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path, prepend_path_to_env_var,
    sysroot_dir, EXIT_ERR, LIB_PATH,
};

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("Failed to run rustc-flux, error={e}");
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> Result<i32> {
    let flux_driver_path = get_flux_driver_path()?;
    let rust_toolchain = get_rust_toolchain()?;
    let ld_library_path = get_rustc_driver_lib_path(&rust_toolchain)?;
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    let exit_code = Command::new(flux_driver_path)
        // Skip the invocation of rustc-flux itself
        .args(env::args().skip(1))
        .arg("-L")
        .arg(sysroot_dir())
        .arg("--extern")
        .arg("flux_rs")
        .env(LIB_PATH, extended_lib_path)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
