//! Installing and uninstalling a sysroot, shared by `cargo x install` and `cargo flux self`.
//!
//! Every function prints what it does to stderr, in the form of the equivalent shell command.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use anyhow::anyhow;

use crate::{bin_dir, bin_path};

/// Binaries in the sysroot that are linked from cargo's `bin` directory, which is where cargo looks
/// for external subcommands and is usually on the `PATH`.
pub const LINKED_BINARIES: &[&str] = &["cargo-flux", "flux"];

/// A solver that can be bundled in the sysroot's `bin` directory.
pub struct BundledSolver {
    pub name: &'static str,
    /// Argument that makes the solver print its version, used to check that it runs.
    pub version_arg: &'static str,
}

impl BundledSolver {
    /// Whether the solver bundled in `sysroot` runs on this machine.
    pub fn runs(&self, sysroot: &Path) -> bool {
        Command::new(bin_path(sysroot, self.name))
            .arg(self.version_arg)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success())
    }
}

pub const FIXPOINT: BundledSolver =
    BundledSolver { name: "fixpoint", version_arg: "--numeric-version" };

pub const Z3: BundledSolver = BundledSolver { name: "z3", version_arg: "--version" };

pub const BUNDLED_SOLVERS: &[BundledSolver] = &[FIXPOINT, Z3];

/// Returns the paths in cargo's `bin` directory the [`LINKED_BINARIES`] are linked from.
pub fn binary_links() -> anyhow::Result<Vec<PathBuf>> {
    let cargo_bin = home::cargo_home()?.join("bin");
    Ok(LINKED_BINARIES
        .iter()
        .map(|name| cargo_bin.join(format!("{name}{}", env::consts::EXE_SUFFIX)))
        .collect())
}

/// Links the [`LINKED_BINARIES`] in `sysroot` from cargo's `bin` directory, replacing whatever is
/// there. The links point to `sysroot` itself rather than to the directory it resolves to, so they
/// keep working when `sysroot` is replaced. Windows doesn't have unprivileged symlinks, so there
/// the binaries are copied instead.
pub fn link_binaries(sysroot: &Path) -> anyhow::Result<()> {
    for (name, link) in LINKED_BINARIES.iter().zip(binary_links()?) {
        if let Some(parent) = link.parent() {
            create_dir(parent)?;
        }
        // Create the link next to its final location and rename it there, so it's replaced
        // atomically.
        let tmp = sibling_path(&link, "tmp");
        remove_path(&tmp)?;
        symlink_or_copy(&bin_path(sysroot, name), &tmp)?;
        if cfg!(windows) {
            // Windows doesn't replace an executable that is running, e.g., the `cargo-flux` doing
            // the installation.
            remove_executable(&link)?;
        }
        rename(&tmp, &link)?;
    }
    Ok(())
}

#[cfg(unix)]
fn symlink_or_copy(target: &Path, link: &Path) -> anyhow::Result<()> {
    eprintln!("$ ln -s {} {}", target.display(), link.display());
    std::os::unix::fs::symlink(target, link).map_err(|err| {
        anyhow!("failed to link `{}` to `{}`: {err}", link.display(), target.display())
    })
}

#[cfg(not(unix))]
fn symlink_or_copy(target: &Path, link: &Path) -> anyhow::Result<()> {
    copy_file(target, link)
}

/// Whether `link` was created by [`link_binaries`] for `sysroot`. On Windows, where the binaries
/// are copied, any file is assumed to be.
fn is_link_to(link: &Path, sysroot: &Path) -> bool {
    if cfg!(unix) {
        fs::read_link(link).is_ok_and(|target| target.starts_with(bin_dir(sysroot)))
    } else {
        link.is_file()
    }
}

/// Removes `sysroot` and the links [`link_binaries`] created for it.
pub fn uninstall(sysroot: &Path) -> anyhow::Result<()> {
    for link in binary_links()? {
        if is_link_to(&link, sysroot) {
            remove_executable(&link)?;
        }
    }
    eprintln!("$ rm -rf {}", sysroot.display());
    remove_path(sysroot)
}

/// Removes the executable `path`, which may be running. Windows doesn't remove a running
/// executable, but does rename it, so there it's renamed to `<path>.old` if it can't be removed.
/// That file is removed the next time.
fn remove_executable(path: &Path) -> anyhow::Result<()> {
    if !cfg!(windows) {
        eprintln!("$ rm {}", path.display());
        return remove_path(path);
    }
    let old = sibling_path(path, "old");
    let _ = remove_path(&old);
    if path.symlink_metadata().is_err() || remove_path(path).is_ok() {
        return Ok(());
    }
    rename(path, &old)
}

/// Replaces `dst` with `src`. Where the platform and filesystem support it, the two are exchanged
/// atomically. Elsewhere (e.g., on Windows), `dst` is moved out of the way first, so it briefly
/// doesn't exist.
pub fn replace_dir(src: &Path, dst: &Path) -> anyhow::Result<()> {
    if !dst.exists() {
        return rename(src, dst);
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        use rustix::fs::{CWD, RenameFlags, renameat_with};
        eprintln!("$ exchange {} {}", src.display(), dst.display());
        if renameat_with(CWD, src, CWD, dst, RenameFlags::EXCHANGE).is_ok() {
            // `src` now holds the old contents of `dst`
            return remove_path(src);
        }
    }
    let old = sibling_path(dst, "old");
    remove_path(&old)?;
    rename(dst, &old)?;
    rename(src, dst)?;
    remove_path(&old)
}

/// Downloads `url` into the file `dst` with `curl`.
pub fn download(url: &str, dst: &Path) -> anyhow::Result<()> {
    eprintln!("$ curl -o {} {url}", dst.display());
    let status = Command::new("curl")
        .args(["--proto", "=https", "--tlsv1.2", "-fsSL", "--retry", "3", "-o"])
        .arg(dst)
        .arg(url)
        .status()
        .map_err(|err| {
            anyhow!("failed to run `curl`, which is needed to download `{url}`: {err}")
        })?;
    if !status.success() {
        return Err(anyhow!("failed to download `{url}`: `curl` exited with {status}"));
    }
    Ok(())
}

pub fn rename(src: &Path, dst: &Path) -> anyhow::Result<()> {
    eprintln!("$ mv {} {}", src.display(), dst.display());
    fs::rename(src, dst).map_err(|err| {
        anyhow!("failed to rename `{}` to `{}`: {err}", src.display(), dst.display())
    })
}

/// Returns `path` with `.{suffix}` appended, e.g., `sysroot` becomes `sysroot.new`.
pub fn sibling_path(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{suffix}"));
    path.with_file_name(name)
}

/// Copies the file `src` to `dst`, or into `dst` if it's a directory.
pub fn copy_file<S: AsRef<Path>, D: AsRef<Path>>(src: S, dst: D) -> anyhow::Result<()> {
    let src = src.as_ref();
    let dst = dst.as_ref();
    eprintln!("$ cp {} {}", src.display(), dst.display());

    let mut _tmp;
    let mut dst = dst;
    if dst.is_dir()
        && let Some(file_name) = src.file_name()
    {
        _tmp = dst.join(file_name);
        dst = &_tmp;
    }
    fs::copy(src, dst).map_err(|err| {
        anyhow!("failed to copy `{}` to `{}`: {err}", src.display(), dst.display())
    })?;

    Ok(())
}

/// Removes the file or directory at `path`. A symlink is removed itself, not what it points to.
pub fn remove_path(path: &Path) -> anyhow::Result<()> {
    match path.symlink_metadata() {
        Ok(meta) => {
            if meta.is_dir() { remove_dir_all(path) } else { fs::remove_file(path) }
                .map_err(|err| anyhow!("failed to remove path `{}`: {err}", path.display()))
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(anyhow!("failed to remove path `{}`: {err}", path.display())),
    }
}

#[cfg(not(windows))]
fn remove_dir_all(path: &Path) -> io::Result<()> {
    fs::remove_dir_all(path)
}

// Copied from xshell
#[cfg(windows)]
fn remove_dir_all(path: &Path) -> io::Result<()> {
    for _ in 0..99 {
        if fs::remove_dir_all(path).is_ok() {
            return Ok(());
        }
        std::thread::sleep(std::time::Duration::from_millis(10))
    }
    fs::remove_dir_all(path)
}

pub fn create_dir(path: &Path) -> anyhow::Result<()> {
    fs::create_dir_all(path)
        .map_err(|err| anyhow!("failed to create directory `{}`: {err}", path.display()))
}
