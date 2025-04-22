use std::{
    env,
    process::{Command, exit},
};

use anyhow::Result;
use flux_bin::utils::{
    EXIT_ERR, LIB_PATH, get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path,
    prepend_path_to_env_var, sysroot_dir,
};

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("failed to run `flux`, error={e}");
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> Result<i32> {
    let sysroot = sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&sysroot)?;
    let rust_toolchain = get_rust_toolchain()?;
    let ld_library_path = get_rustc_driver_lib_path(&rust_toolchain)?;
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    let exit_code = Command::new(flux_driver_path)
        // Skip the invocation of `flux` itself
        .args(env::args().skip(1))
        .arg("-L")
        .arg(sysroot)
        .args(["--extern", "flux_rs", "-Fverify=on"])
        .env(LIB_PATH, extended_lib_path)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
