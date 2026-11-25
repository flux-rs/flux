use std::{
    env,
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Result, anyhow};

#[cfg(target_os = "windows")]
pub const LIB_PATH: &str = "PATH";
#[cfg(any(target_os = "linux", target_os = "freebsd"))]
pub const LIB_PATH: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
pub const LIB_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

use flux_sysroot::SysrootManifest;
pub use flux_sysroot::{FLUX_SYSROOT, flux_sysroot_dir, lib_dir};

pub const EXIT_ERR: i32 = -1;

const FLUX_DRIVER: &str = "FLUX_DRIVER";

pub fn get_flux_driver_path(sysroot: &Path) -> Result<PathBuf> {
    let path = env::var_os(FLUX_DRIVER)
        .map_or_else(|| flux_sysroot::bin_path(sysroot, "flux-driver"), PathBuf::from);
    if !path.is_file() {
        return Err(anyhow!("path to flux-driver {:?} does not exist or is not a file", path));
    }
    Ok(path)
}

/// Reads the manifest of `sysroot`, exiting with an error suggesting to reinstall Flux if it's
/// invalid.
pub fn read_sysroot_manifest(sysroot: &Path) -> SysrootManifest {
    SysrootManifest::read(sysroot).unwrap_or_else(|err| {
        eprintln!("error: {err}");
        std::process::exit(EXIT_ERR)
    })
}

pub fn get_binary_path(toolchain: &str, bin: &str) -> anyhow::Result<PathBuf> {
    let output = Command::new("rustup")
        .args(["which", "--toolchain", toolchain, bin])
        .output()
        .map_err(|e| anyhow!("failed to run `rustup which`: {e}"))?;

    if !output.status.success() {
        return Err(anyhow!("`rustup which` failed: {}", String::from_utf8_lossy(&output.stderr)));
    }

    Ok(PathBuf::from(
        String::from_utf8(output.stdout)
            .map_err(|e| anyhow!("invalid utf8 from `rustup which` output: {e}"))?
            .trim()
            .to_string(),
    ))
}

pub fn get_rust_sysroot(toolchain: &str) -> Result<PathBuf> {
    let out = Command::new("rustc")
        .arg(format!("+{toolchain}"))
        .args(["--print", "sysroot"])
        .output()?;
    bytes_to_pathbuf(out.stdout)
}

/// Path from where to load the rustc-driver library from
pub fn get_rust_lib_path(sysroot: &Path) -> PathBuf {
    if cfg!(windows) { sysroot.join("bin") } else { sysroot.join("lib") }
}

/// Prepends the path so that it's the first checked.
pub fn prepend_path_to_env_var(var_name: &str, new_path: PathBuf) -> Result<OsString> {
    let mut paths = match env::var(var_name) {
        Ok(paths) => env::split_paths(&paths).collect(),
        Err(env::VarError::NotPresent) => vec![],
        Err(e) => Err(e)?,
    };
    paths.insert(0, new_path);
    env::join_paths(paths).map_err(anyhow::Error::from)
}

fn bytes_to_pathbuf(input: Vec<u8>) -> Result<PathBuf> {
    Ok(PathBuf::from(String::from_utf8(input)?.trim()))
}

/// Prints the version of the active Flux sysroot. The version is recorded in the sysroot manifest when it
/// is built.
pub fn print_version_and_exit(program_name: &str, verbose: bool) -> ! {
    let sysroot = flux_sysroot_dir();
    let manifest = read_sysroot_manifest(&sysroot);
    let version = &manifest.version;
    if verbose {
        println!("{program_name} {} ({})", version.sha_full, version.date);
        println!("sysroot: {}", sysroot.display());
        println!("toolchain: {}", manifest.toolchain);
    } else {
        println!("{program_name} {} ({})", version.sha, version.date);
    }
    std::process::exit(0)
}
