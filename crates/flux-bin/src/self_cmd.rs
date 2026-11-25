//! `cargo flux self`: installing and uninstalling Flux from a prebuilt release.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::anyhow;
use flux_sysroot::{
    FLUX_SYSROOT, SYSROOT_MANIFEST, SysrootManifest, bin_path, default_flux_sysroot_dir,
    install::{
        self, BundledSolver, FIXPOINT, Z3, copy_dir, create_dir, link_binaries, remove_path,
        replace_dir, sibling_path,
    },
};

use crate::cargo_flux_opts::SelfCommand;

pub fn run(command: SelfCommand) -> anyhow::Result<()> {
    match command {
        SelfCommand::Install => install(),
        SelfCommand::Uninstall => uninstall(),
    }
}

/// Installs the sysroot containing the running `cargo-flux` as the default sysroot, together with
/// the toolchain it needs, and links its binaries from cargo's `bin` directory.
fn install() -> anyhow::Result<()> {
    let src = running_sysroot()?;
    let manifest = SysrootManifest::read(&src)?;
    let dst = default_flux_sysroot_dir();

    // First, so a failure leaves the current installation untouched.
    install_toolchain(&manifest)?;

    if !same_dir(&src, &dst) {
        if let Some(parent) = dst.parent() {
            create_dir(parent)?;
        }
        // Copy instead of moving `src`: it may be on another filesystem, and on Windows the
        // running `cargo-flux` keeps it from being moved.
        let staging = sibling_path(&dst, "new");
        remove_path(&staging)?;
        copy_dir(&src, &staging)?;
        remove_broken_solvers(&staging)?;
        replace_dir(&staging, &dst)?;
    }
    link_binaries(&dst)?;

    eprintln!();
    eprintln!(
        "Installed Flux {} ({}) to `{}`",
        manifest.version.sha,
        manifest.version.date,
        dst.display()
    );
    if let Some(sysroot) = env::var_os(FLUX_SYSROOT) {
        eprintln!(
            "warning: `{FLUX_SYSROOT}` is set to `{}`, so Flux won't use this installation",
            sysroot.display()
        );
    }
    Ok(())
}

/// Removes the default sysroot and the links to its binaries. The toolchain and the configuration
/// are left alone.
fn uninstall() -> anyhow::Result<()> {
    let sysroot = default_flux_sysroot_dir();
    let toolchain = SysrootManifest::read(&sysroot)
        .ok()
        .map(|manifest| manifest.toolchain);
    install::uninstall(&sysroot)?;

    eprintln!();
    eprintln!("Uninstalled Flux from `{}`", sysroot.display());
    if let Some(toolchain) = toolchain {
        eprintln!(
            "note: the toolchain Flux used is still installed, remove it with `rustup toolchain uninstall {toolchain}` if nothing else uses it"
        );
    }
    Ok(())
}

/// The sysroot the running `cargo-flux` is in, i.e., `<sysroot>/bin/cargo-flux`.
fn running_sysroot() -> anyhow::Result<PathBuf> {
    let exe = fs::canonicalize(env::current_exe()?)?;
    exe.parent()
        .and_then(Path::parent)
        .filter(|sysroot| sysroot.join(SYSROOT_MANIFEST).is_file())
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            anyhow!(
                "`{}` is not in a Flux sysroot, run `cargo flux self install` from an extracted Flux release",
                exe.display()
            )
        })
}

fn same_dir(a: &Path, b: &Path) -> bool {
    match (fs::canonicalize(a), fs::canonicalize(b)) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

/// Installs, with rustup, the toolchain `manifest` was built with. The minimal profile is enough
/// to run Flux: the components in `rust-toolchain.toml` are only needed to develop it.
fn install_toolchain(manifest: &SysrootManifest) -> anyhow::Result<()> {
    let mut cmd = Command::new("rustup");
    cmd.args(["toolchain", "install", &manifest.toolchain, "--profile", "minimal"]);
    eprintln!(
        "$ rustup {}",
        cmd.get_args()
            .map(|arg| arg.to_string_lossy())
            .collect::<Vec<_>>()
            .join(" ")
    );
    let status = cmd.status().map_err(|err| {
        anyhow!("failed to run `rustup`, which Flux needs (see https://rustup.rs): {err}")
    })?;
    if !status.success() {
        return Err(anyhow!("failed to install the toolchain `{}`", manifest.toolchain));
    }
    Ok(())
}

/// Removes the solvers bundled in `sysroot` that don't run on this machine, e.g., on an older OS
/// than the release was built for, so Flux looks them up in `PATH` instead.
fn remove_broken_solvers(sysroot: &Path) -> anyhow::Result<()> {
    let is_bundled = |solver: &BundledSolver| bin_path(sysroot, solver.name).exists();
    let remove = |solver: &BundledSolver, reason: &str| {
        eprintln!("warning: {reason}, Flux will look `{}` up in PATH", solver.name);
        remove_path(&bin_path(sysroot, solver.name))
    };
    if is_bundled(&FIXPOINT) && !FIXPOINT.runs(sysroot) {
        remove(&FIXPOINT, "the bundled `fixpoint` doesn't run on this machine")?;
        // z3 is only bundled to be passed to the bundled fixpoint.
        if is_bundled(&Z3) {
            remove(&Z3, "the bundled `z3` is only used with the bundled `fixpoint`")?;
        }
    } else if is_bundled(&Z3) && !Z3.runs(sysroot) {
        remove(&Z3, "the bundled `z3` doesn't run on this machine")?;
    }
    Ok(())
}
