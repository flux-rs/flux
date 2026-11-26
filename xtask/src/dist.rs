//! Release archives of the Flux sysroot, built by `cargo x dist`.

use std::{fs, path::Path, process::Command};

use anyhow::anyhow;
use flux_sysroot::install::remove_path;

use crate::{
    install_sysroot, solvers::BundleSolvers, workspace_root, BuildLibs, Dist, FluxLib, Profile,
    SysrootConfig,
};

/// Builds the sysroot for the host into `<out-dir>/sysroot`, with the solvers bundled, and packs it
/// into `<out-dir>/flux-<host>.tar.gz`. The archive contains a top-level `sysroot` directory, so
/// extracting it in the Flux home gives the default sysroot.
pub(crate) fn dist(args: &Dist, rust_fixpoint: bool) -> anyhow::Result<()> {
    let out_dir = args
        .out_dir
        .clone()
        .unwrap_or_else(|| workspace_root().join("target").join("dist"));
    let sysroot = out_dir.join("sysroot");
    // Don't leave an archive from an earlier run behind if this one fails.
    let archive = out_dir.join(format!("flux-{}.tar.gz", host_triple()?));
    remove_path(&archive)?;
    let config = SysrootConfig {
        profile: Profile::Release,
        rust_fixpoint,
        dst: sysroot.clone(),
        build_libs: BuildLibs { force: false, libs: FluxLib::ALL },
        // A release must not ship without a solver.
        bundle_solvers: BundleSolvers::Yes { required: true },
    };
    install_sysroot(&config)?;

    write_archive(&sysroot, &archive)
}

/// The target triple of the host, as reported by the pinned `rustc`.
fn host_triple() -> anyhow::Result<String> {
    let output = Command::new("rustc")
        .arg("-vV")
        .current_dir(workspace_root())
        .output()
        .map_err(|err| anyhow!("failed to run `rustc -vV`: {err}"))?;
    String::from_utf8(output.stdout)?
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::to_string)
        .ok_or_else(|| anyhow!("`rustc -vV` didn't report the host"))
}

/// Packs `sysroot` into the `.tar.gz` file `archive`, under a top-level `sysroot` directory.
fn write_archive(sysroot: &Path, archive: &Path) -> anyhow::Result<()> {
    eprintln!("$ tar -czf {} sysroot", archive.display());
    let file = fs::File::create(archive)
        .map_err(|err| anyhow!("failed to create `{}`: {err}", archive.display()))?;
    let mut builder =
        tar::Builder::new(flate2::write::GzEncoder::new(file, flate2::Compression::default()));
    builder.append_dir_all("sysroot", sysroot)?;
    builder.into_inner()?.finish()?;
    Ok(())
}
