#![feature(exit_status_error)]

use std::{env, process::Command};

use anyhow::Result;
use flux_bin::utils::{
    LIB_PATH, flux_sysroot_dir, get_flux_driver_path, get_rust_lib_path, get_rust_sysroot,
    prepend_path_to_env_var, print_version_and_exit, read_sysroot_manifest,
};
use flux_sysroot::SysrootManifest;

fn main() -> Result<()> {
    // Handle the version flags here, otherwise rustc would print its own version.
    if env::args().any(|arg| matches!(arg.as_str(), "--version" | "-V" | "-vV" | "-Vv")) {
        let verbose =
            env::args().any(|arg| matches!(arg.as_str(), "--verbose" | "-v" | "-vV" | "-Vv"));
        print_version_and_exit("flux", verbose);
    }

    let flux_sysroot = flux_sysroot_dir();
    let manifest = read_sysroot_manifest(&flux_sysroot);
    let flux_driver_path = get_flux_driver_path(&flux_sysroot)?;
    let rust_sysroot = get_rust_sysroot(&manifest.toolchain)?;
    let ld_library_path = get_rust_lib_path(&rust_sysroot);
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    Command::new(flux_driver_path)
        // Skip the invocation of `flux` itself
        .args(env::args().skip(1))
        // Transitive deps ignore `--extern`, so they still need a search path.
        .arg("-L")
        .arg(&flux_sysroot)
        .arg(format!("-Fsysroot={}", flux_sysroot.display()))
        .args(SysrootManifest::extern_args(&flux_sysroot))
        .arg("-Fverify=on")
        .env(LIB_PATH, extended_lib_path)
        .status()?
        .exit_ok()?;

    Ok(())
}
