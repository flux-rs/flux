//! `cargo flux self`: installing, updating, and uninstalling Flux from prebuilt releases.
//!
//! Releases are published by the `nightly` workflow: the moving `nightly` release, and dated
//! `nightly-yyyy-mm-dd` copies. Each has a `manifest.json`, see [`ReleaseManifest`], and one
//! `flux-<target>.tar.gz` archive per target, holding a `sysroot` directory.

use std::{
    collections::BTreeMap,
    env, fs,
    io::{self, IsTerminal},
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::anyhow;
use flux_sysroot::{
    FLUX_SYSROOT, SYSROOT_MANIFEST, SysrootManifest, bin_path, default_flux_sysroot_dir,
    install::{
        self, copy_dir, create_dir, download, link_binaries, remove_broken_solvers, remove_path,
        replace_dir, sibling_path,
    },
};
use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::cargo_flux_opts::SelfCommand;

pub fn run(command: SelfCommand) -> anyhow::Result<()> {
    match command {
        SelfCommand::Install => install(),
        SelfCommand::Update { to } => update(to.as_deref().unwrap_or(NIGHTLY)),
        SelfCommand::Uninstall => uninstall(),
    }
}

/// Installs the sysroot containing the running `cargo-flux` as the default sysroot, together with
/// the toolchain it needs, and links its binaries from cargo's `bin` directory.
fn install() -> anyhow::Result<()> {
    let src = running_sysroot()?;
    let manifest = SysrootManifest::read(&src)?;
    let dst = default_flux_sysroot_dir();
    let previous_toolchain = SysrootManifest::read(&dst)
        .ok()
        .map(|previous| previous.toolchain);

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
        remove_broken_solvers(&staging, false)?;
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
    if let Some(previous) = previous_toolchain
        && previous != manifest.toolchain
    {
        offer_to_uninstall_toolchain(&previous)?;
    }
    Ok(())
}

/// Asks whether to uninstall `toolchain`, the one the previous installation used, which may also be
/// used by something else. Without a terminal to ask in, it only says how to do it.
fn offer_to_uninstall_toolchain(toolchain: &str) -> anyhow::Result<()> {
    eprintln!();
    if !io::stdin().is_terminal() {
        eprintln!(
            "note: Flux no longer uses the toolchain `{toolchain}`, remove it with `rustup toolchain uninstall {toolchain}` if nothing else uses it"
        );
        return Ok(());
    }
    eprint!(
        "Flux no longer uses the toolchain `{toolchain}`. Uninstall it, if nothing else uses it? [y/N] "
    );
    let mut answer = String::new();
    io::stdin().read_line(&mut answer)?;
    if !matches!(answer.trim(), "y" | "Y" | "yes") {
        return Ok(());
    }
    let status = Command::new("rustup")
        .args(["toolchain", "uninstall", toolchain])
        .status()
        .map_err(|err| anyhow!("failed to run `rustup`: {err}"))?;
    if !status.success() {
        eprintln!("warning: failed to uninstall the toolchain `{toolchain}`");
    }
    Ok(())
}

/// Where the releases are downloaded from, followed by `/<tag>/<file>`.
const RELEASES_URL: &str = "https://github.com/flux-rs/flux/releases/download";

/// The release that always points to the latest build.
const NIGHTLY: &str = "nightly";

/// The `manifest.json` of a release.
#[derive(Deserialize)]
struct ReleaseManifest {
    /// Commit the release was built from.
    commit: String,
    /// The archive of each target.
    targets: BTreeMap<String, ReleaseArchive>,
}

#[derive(Deserialize)]
struct ReleaseArchive {
    url: String,
    sha256: String,
}

/// The target of the release archives for this machine, if there are any. Keep in sync with the
/// `build` job of `.github/workflows/nightly.yml`.
fn release_target() -> anyhow::Result<&'static str> {
    match (env::consts::OS, env::consts::ARCH) {
        ("linux", "x86_64") => Ok("x86_64-unknown-linux-gnu"),
        ("macos", "aarch64") => Ok("aarch64-apple-darwin"),
        ("windows", "x86_64") => Ok("x86_64-pc-windows-msvc"),
        (os, arch) => Err(anyhow!("there are no Flux releases for {arch}-{os}")),
    }
}

/// Installs the release `tag`, unless it's already installed. The release's archive is extracted
/// next to the default sysroot, and the `cargo-flux` in it installs it with `cargo flux self
/// install`, so the installation is always done by the version being installed.
fn update(tag: &str) -> anyhow::Result<()> {
    let target = release_target()?;
    let sysroot = default_flux_sysroot_dir();
    let tmp = sibling_path(&sysroot, "download");
    remove_path(&tmp)?;
    create_dir(&tmp)?;
    let result = download_and_install(tag, target, &sysroot, &tmp);
    remove_path(&tmp)?;
    result
}

fn download_and_install(tag: &str, target: &str, sysroot: &Path, tmp: &Path) -> anyhow::Result<()> {
    let manifest_path = tmp.join("manifest.json");
    download(&format!("{RELEASES_URL}/{tag}/manifest.json"), &manifest_path).map_err(|err| {
        anyhow!("{err}\nnote: the releases are listed in https://github.com/flux-rs/flux/releases")
    })?;
    let manifest: ReleaseManifest = serde_json::from_str(&fs::read_to_string(&manifest_path)?)
        .map_err(|err| anyhow!("invalid manifest of the release `{tag}`: {err}"))?;

    if let Ok(installed) = SysrootManifest::read(sysroot)
        && installed.version.sha_full == manifest.commit
    {
        eprintln!(
            "Flux {} ({}) is already installed",
            installed.version.sha, installed.version.date
        );
        return Ok(());
    }

    let archive = manifest
        .targets
        .get(target)
        .ok_or_else(|| anyhow!("the release `{tag}` has no archive for `{target}`"))?;
    let archive_path = tmp.join(format!("flux-{target}.tar.gz"));
    eprintln!("Downloading {}", archive.url);
    download(&archive.url, &archive_path)?;
    let sha256 = sha256(&archive_path)?;
    if !sha256.eq_ignore_ascii_case(&archive.sha256) {
        return Err(anyhow!(
            "the checksum of `{}` doesn't match the release manifest: expected {}, got {sha256}",
            archive.url,
            archive.sha256
        ));
    }

    tar::Archive::new(flate2::read::GzDecoder::new(fs::File::open(&archive_path)?))
        .unpack(tmp)
        .map_err(|err| anyhow!("failed to extract `{}`: {err}", archive_path.display()))?;

    let cargo_flux = bin_path(&tmp.join("sysroot"), "cargo-flux");
    let status = Command::new(&cargo_flux)
        .args(["flux", "self", "install"])
        .status()
        .map_err(|err| anyhow!("failed to run `{}`: {err}", cargo_flux.display()))?;
    if !status.success() {
        return Err(anyhow!("failed to install the release `{tag}`"));
    }
    Ok(())
}

/// The SHA-256 checksum of the file `path`, in hex.
fn sha256(path: &Path) -> anyhow::Result<String> {
    let mut hasher = Sha256::new();
    io::copy(&mut fs::File::open(path)?, &mut hasher)?;
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

/// Removes the default sysroot and the links to its binaries. The toolchain and the configuration
/// are left alone.
fn uninstall() -> anyhow::Result<()> {
    let sysroot = default_flux_sysroot_dir();
    let toolchain = SysrootManifest::read(&sysroot)
        .ok()
        .map(|manifest| manifest.toolchain);
    install::uninstall(&sysroot)?;

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
    let status = cmd.status().map_err(|err| {
        anyhow!("failed to run `rustup`, which Flux needs (see https://rustup.rs): {err}")
    })?;
    if !status.success() {
        return Err(anyhow!("failed to install the toolchain `{}`", manifest.toolchain));
    }
    Ok(())
}
