//! Prebuilt solvers bundled into the sysroot by `cargo x install --bundle-solvers`.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use anyhow::anyhow;

use crate::{remove_path, CommandExt};

/// Whether to bundle prebuilt solvers into the sysroot.
#[derive(Clone, Copy)]
pub(crate) enum BundleSolvers {
    /// Don't bundle solvers. Flux looks them up in `PATH`.
    No,
    /// Bundle the solvers that have a prebuilt binary for the host and run on it.
    Yes {
        /// Fail if a solver can't be bundled. Otherwise, it's skipped with a warning and Flux looks
        /// it up in `PATH`.
        required: bool,
    },
}

/// A solver downloaded into the sysroot by `cargo x install --bundle-solvers`.
struct Solver {
    name: &'static str,
    /// URL of the release archive containing the solver for the host, if there is one.
    archive_url: fn() -> Option<String>,
    /// Argument that makes the solver print its version, used to check it runs on the host.
    version_arg: &'static str,
}

const FIXPOINT: Solver = Solver {
    name: "fixpoint",
    archive_url: fixpoint_archive_url,
    version_arg: "--numeric-version",
};

const Z3: Solver = Solver { name: "z3", archive_url: z3_archive_url, version_arg: "--version" };

fn fixpoint_archive_url() -> Option<String> {
    let asset = match (env::consts::OS, env::consts::ARCH) {
        ("linux", "x86_64") => "fixpoint-x86_64-linux-gnu.tar.gz",
        ("macos", "aarch64") => "fixpoint-aarch64-apple-darwin.tar.gz",
        ("windows", "x86_64") => "fixpoint-x86_64-pc-windows.zip",
        _ => return None,
    };
    Some(format!(
        "https://github.com/ucsd-progsys/liquid-fixpoint/releases/download/nightly/{asset}"
    ))
}

/// The z3 version CI tests with.
const Z3_VERSION: &str = "4.15.3";

fn z3_archive_url() -> Option<String> {
    let platform = match (env::consts::OS, env::consts::ARCH) {
        // Only the platforms with a prebuilt fixpoint, see `fixpoint_archive_url`
        ("linux", "x86_64") => "x64-glibc-2.39",
        ("macos", "aarch64") => "arm64-osx-13.7.6",
        ("windows", "x86_64") => "x64-win",
        _ => return None,
    };
    Some(format!(
        "https://github.com/Z3Prover/z3/releases/download/z3-{Z3_VERSION}/z3-{Z3_VERSION}-{platform}.zip"
    ))
}

/// Downloads fixpoint and z3 into `bin`. Flux looks up the solvers that aren't bundled in `PATH`.
///
/// z3 is only bundled together with a fixpoint that supports `--solver-path`. Otherwise, Flux would
/// pass the bundled z3 to a fixpoint that can't take it.
pub(crate) fn bundle(bin: &Path, required: bool) -> anyhow::Result<()> {
    let Some(fixpoint) = download_solver(&FIXPOINT, bin, required)? else {
        return skip(required, "not bundling `z3` without `fixpoint`");
    };
    if !supports_solver_path(&fixpoint) {
        return skip(
            required,
            "not bundling `z3` because the prebuilt `fixpoint` doesn't support `--solver-path`",
        );
    }
    download_solver(&Z3, bin, required)?;
    Ok(())
}

/// Gives up on bundling a solver: an error if `required`, and a warning otherwise.
fn skip(required: bool, reason: &str) -> anyhow::Result<()> {
    if required {
        return Err(anyhow!("{reason}"));
    }
    eprintln!("warning: {reason}, Flux will look it up in PATH");
    Ok(())
}

/// Downloads `solver` into `bin` and returns its path. Returns `None`, or an error if `required`,
/// if there is no prebuilt binary for the host or if it doesn't run on it.
fn download_solver(solver: &Solver, bin: &Path, required: bool) -> anyhow::Result<Option<PathBuf>> {
    let Some(url) = (solver.archive_url)() else {
        let reason = format!(
            "there is no prebuilt `{}` for {}-{}",
            solver.name,
            env::consts::ARCH,
            env::consts::OS,
        );
        skip(required, &reason)?;
        return Ok(None);
    };
    let exe = bin.join(format!("{}{}", solver.name, env::consts::EXE_SUFFIX));
    let archive = bin.join(url.rsplit('/').next().unwrap_or(solver.name));
    download(&url, &archive)?;
    extract_executable(&archive, &exe)?;
    remove_path(&archive)?;

    let runs = Command::new(&exe)
        .arg(solver.version_arg)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success());
    if !runs {
        remove_path(&exe)?;
        skip(required, &format!("the prebuilt `{}` doesn't run on this machine", solver.name))?;
        return Ok(None);
    }
    Ok(Some(exe))
}

/// Whether `fixpoint` supports `--solver-path`, i.e., lists it in its help.
fn supports_solver_path(fixpoint: &Path) -> bool {
    Command::new(fixpoint)
        .arg("--help")
        .stderr(Stdio::null())
        .output()
        .is_ok_and(|output| String::from_utf8_lossy(&output.stdout).contains("--solver-path"))
}

fn download(url: &str, dst: &Path) -> anyhow::Result<()> {
    Command::new("curl")
        .args(["--proto", "=https", "--tlsv1.2", "-fsSL", "--retry", "3", "-o"])
        .arg(dst)
        .arg(url)
        .run()
        .map_err(|err| anyhow!("failed to download `{url}` (this requires `curl`): {err}"))
}

/// Extracts the file named like `exe` from the `.zip` or `.tar.gz` `archive` into `exe`.
fn extract_executable(archive: &Path, exe: &Path) -> anyhow::Result<()> {
    eprintln!("$ extract {} from {}", exe.display(), archive.display());
    let name = exe.file_name().unwrap_or_default();
    let not_found = || anyhow!("`{}` does not contain `{}`", archive.display(), name.display());
    let file = fs::File::open(archive)?;
    let mut out = fs::File::create(exe)?;
    if archive.extension().is_some_and(|ext| ext == "zip") {
        let mut zip = zip::ZipArchive::new(file)?;
        let index = (0..zip.len())
            .find(|&i| {
                zip.by_index(i).is_ok_and(|entry| {
                    entry.is_file() && Path::new(entry.name()).file_name() == Some(name)
                })
            })
            .ok_or_else(not_found)?;
        io::copy(&mut zip.by_index(index)?, &mut out)?;
    } else {
        let mut tar = tar::Archive::new(flate2::read::GzDecoder::new(file));
        let mut entry = tar
            .entries()?
            .filter_map(Result::ok)
            .find(|entry| {
                entry.header().entry_type().is_file()
                    && entry
                        .path()
                        .is_ok_and(|path| path.file_name() == Some(name))
            })
            .ok_or_else(not_found)?;
        io::copy(&mut entry, &mut out)?;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(exe, fs::Permissions::from_mode(0o755))?;
    }
    Ok(())
}
