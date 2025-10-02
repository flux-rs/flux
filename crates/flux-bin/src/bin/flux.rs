#![feature(exit_status_error)]

use std::{env, process::Command};

use anyhow::Result;
use flux_bin::utils::{
    LIB_PATH, flux_sysroot_dir, get_flux_driver_path, get_rust_lib_path, get_rust_sysroot,
    get_rust_toolchain, get_version, prepend_path_to_env_var,
};

fn main() -> Result<()> {
    if env::args().any(|arg| arg == "--version" || arg == "-V") {
        println!("flux {}", get_version());
        std::process::exit(0);
    }

    let flux_sysroot = flux_sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&flux_sysroot)?;
    let rust_sysroot = get_rust_sysroot(&get_rust_toolchain()?)?;
    let ld_library_path = get_rust_lib_path(&rust_sysroot);
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    Command::new(flux_driver_path)
        // Skip the invocation of `flux` itself
        .args(env::args().skip(1))
        .arg("-L")
        .arg(flux_sysroot)
        .args(["--extern", "flux_rs", "-Fverify=on"])
        .env(LIB_PATH, extended_lib_path)
        .status()?
        .exit_ok()?;

    Ok(())
}
