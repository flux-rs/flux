#![feature(variant_count)]

mod solvers;

use std::{
    collections::BTreeMap,
    env,
    ffi::OsStr,
    fs, io,
    mem::variant_count,
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
};

use anyhow::anyhow;
use cargo_metadata::{
    camino::{Utf8Path, Utf8PathBuf},
    Artifact, Message, TargetKind,
};
use flux_sysroot::{
    bin_dir, bin_path, default_flux_sysroot_dir,
    dev::{default_flags, Suite},
    lib_dir, parse_toolchain_file, FluxVersion, SysrootCrate, SysrootManifest, FLUX_SYSROOT,
    SYSROOT_MANIFEST,
};

xflags::xflags! {
    cmd xtask {
        /// If true, run all cargo commands with `--offline`
        optional --offline
        /// If true, run cargo build commands with --features rust-fixpiont
        optional --rust-fixpoint
        /// Run regression tests
        cmd test {
            /// Only run tests containing `filter` as a substring.
            optional filter: String
            /// Run only the named suite(s). May be repeated. If omitted, all suites run.
            repeated --suite suite: Suite
            /// Timeout in seconds for each fixpoint query (passed as `-Ffixpoint-timeout`)
            optional --fixpoint-timeout seconds: u64
        }
        /// Run lean benchmarks: emit lean files for each test in tests/pos/
        cmd lean-bench {
            /// Only run tests containing `filter` as a substring.
            optional filter: String
        }
        /// Run the `flux` binary on the given input file.
        cmd run {
            /// Input file
            required input: PathBuf
            /// Extra options to pass to the `flux` binary, e.g., `cargo x run file.rs -- -Zdump-mir=renumber`
            repeated opts: String
            /// Do not build Flux libs for extern specs
            optional --no-extern-specs
        }
        /// Expand Flux macros
        cmd expand {
            /// Input file
            required input: PathBuf
        }
        /// Install the Flux sysroot (binaries and precompiled libraries) to `~/.flux/sysroot` and link
        /// `flux` and `cargo-flux` from `~/.cargo/bin`
        cmd install {
            /// Select build profile for the `flux-driver`, either 'release', 'dev', or 'profiling'. Default 'release'
            optional --profile profile: Profile
            /// Do not install Flux libs or extern specs
            optional --no-extern-specs
            /// Download prebuilt `fixpoint` and `z3` into the sysroot, if there are any for this platform
            optional --bundle-solvers
        }
        /// Uninstall Flux binaries and libraries
        cmd uninstall { }
        /// Generate precompiled libraries
        cmd build-sysroot { }
        /// Build the documentation
        cmd doc { }
        /// Start blick, which runs Flux on programs and shows its checker trace in the browser. The
        /// page can open the regression tests in `tests/tests`
        cmd blick {
            /// The port to listen on (on 127.0.0.1). Default 8765
            optional --port port: u16
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Profile {
    Release,
    Dev,
    Profiling,
}

impl Profile {
    fn as_str(self) -> &'static str {
        match self {
            Profile::Release => "release",
            Profile::Dev => "dev",
            Profile::Profiling => "profiling",
        }
    }
}

impl std::str::FromStr for Profile {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "release" => Ok(Self::Release),
            "dev" => Ok(Self::Dev),
            "profiling" => Ok(Self::Profiling),
            _ => Err("invalid profile"),
        }
    }
}

fn main() -> anyhow::Result<()> {
    let cmd = match Xtask::from_env() {
        Ok(cmd) => cmd,
        Err(err) => {
            if err.is_help() {
                println!("{}", Xtask::HELP_);
                std::process::exit(0);
            } else {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
    };

    if cmd.offline {
        // Inherited by every cargo we run, including the one `cargo-flux` runs to build the libraries.
        // SAFETY: xtask is single-threaded, so nothing reads the environment concurrently.
        unsafe { env::set_var("CARGO_NET_OFFLINE", "true") };
        if matches!(&cmd.subcommand, XtaskCmd::Install(args) if args.bundle_solvers) {
            return Err(anyhow!("`--bundle-solvers` needs to download the solvers, so it can't be used with `--offline`"));
        }
    }

    match cmd.subcommand {
        XtaskCmd::Test(args) => test(args, cmd.rust_fixpoint),
        XtaskCmd::LeanBench(args) => lean_bench(args, cmd.rust_fixpoint),
        XtaskCmd::Run(args) => run(args, cmd.rust_fixpoint),
        XtaskCmd::Install(args) => install(&args, cmd.rust_fixpoint),
        XtaskCmd::Doc(args) => doc(args),
        XtaskCmd::BuildSysroot(_) => {
            let config = SysrootConfig {
                profile: Profile::Dev,
                rust_fixpoint: cmd.rust_fixpoint,
                dst: local_sysroot_dir()?,
                build_libs: BuildLibs { force: true, libs: FluxLib::ALL },
                bundle_solvers: false,
            };
            install_sysroot(&config)?;
            Ok(())
        }
        XtaskCmd::Uninstall(_) => uninstall(),
        XtaskCmd::Expand(args) => expand(args),
        XtaskCmd::Blick(args) => blick(&args),
    }
}

fn run_tests(
    flux_driver: &Utf8Path,
    sysroot: &Path,
    suite: &str,
    filter: Option<&str>,
    fixpoint_timeout: Option<u64>,
) -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["test", "-p", "tests", "--"])
        .args(["--flux-driver", flux_driver.as_str()])
        .args(["--sysroot".as_ref(), sysroot.as_os_str()])
        .args(["--suite", suite])
        .args_if_some(filter, |filter| ["--filter", filter])
        .args_if_some(fixpoint_timeout, |timeout| {
            ["--fixpoint-timeout".to_string(), timeout.to_string()]
        })
        .run()
}

fn test(args: Test, rust_fixpoint: bool) -> anyhow::Result<()> {
    let dst = local_sysroot_dir()?;

    let suites: &[Suite] = if args.suite.is_empty() { Suite::ALL } else { &args.suite };

    for suite in suites {
        let libs = match suite {
            Suite::Basic => &[FluxLib::FluxAttrs],
            Suite::WithDeps => FluxLib::ALL,
        };
        let config = SysrootConfig {
            profile: Profile::Dev,
            rust_fixpoint,
            dst: dst.clone(),
            build_libs: BuildLibs { force: false, libs },
            bundle_solvers: false,
        };
        let flux_driver = install_sysroot(&config)?;
        run_tests(&flux_driver, &dst, suite.name(), args.filter.as_deref(), args.fixpoint_timeout)?;
    }
    Ok(())
}

fn lean_bench(args: LeanBench, rust_fixpoint: bool) -> anyhow::Result<()> {
    use walkdir::WalkDir;

    let config = SysrootConfig {
        profile: Profile::Dev,
        rust_fixpoint,
        dst: local_sysroot_dir()?,
        build_libs: BuildLibs { force: false, libs: FluxLib::ALL },
        bundle_solvers: false,
    };
    let flux_driver = install_sysroot(&config)?;

    let pos_path = PathBuf::from("tests/tests/pos");
    let lean_bench_dir = PathBuf::from("tests/lean_bench");

    if !pos_path.exists() {
        return Err(anyhow!("tests/tests/pos directory not found"));
    }

    // Find all .rs test files
    let test_files: Vec<PathBuf> = WalkDir::new(&pos_path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .map(|e| e.path().to_path_buf())
        .filter(|path| {
            // Apply filter if specified
            if let Some(ref filter) = args.filter {
                path.to_string_lossy().contains(filter)
            } else {
                true
            }
        })
        .collect();

    if test_files.is_empty() {
        if args.filter.is_some() {
            eprintln!("No test files found matching filter: {:?}", args.filter);
        } else {
            eprintln!("No test files found under {:?}", pos_path);
        }
        return Ok(());
    }

    eprintln!("Found {} test files", test_files.len());
    eprintln!("{}", "-".repeat(60));

    let mut failures: Vec<(PathBuf, String)> = Vec::new();
    let mut successes = 0;

    for (i, test_path) in test_files.iter().enumerate() {
        let rel_path = test_path.strip_prefix(&pos_path).unwrap();

        // Create lean output dir: ./tests/lean_bench/<path>/<to>/<file>/
        let mut lean_dir = lean_bench_dir.clone();
        if let Some(parent) = rel_path.parent() {
            if parent != Path::new("") {
                lean_dir.push(parent);
            }
        }
        if let Some(stem) = rel_path.file_stem() {
            lean_dir.push(stem);
        }

        eprint!("[{}/{}] Running: {} ... ", i + 1, test_files.len(), rel_path.display());

        // Create the output directory
        if let Err(e) = fs::create_dir_all(&lean_dir) {
            eprintln!("ERROR");
            failures.push((test_path.clone(), format!("Failed to create directory: {}", e)));
            continue;
        }

        // Build rustc flags
        let mut rustc_flags = default_flags(&config.dst, SysrootManifest::extern_args(&config.dst));
        rustc_flags.push("-Flean=emit".to_string());
        rustc_flags.push(format!("-Flean-dir={}", lean_dir.display()));

        // Run the test
        let result = Command::new(&flux_driver)
            .args(&rustc_flags)
            .arg(test_path)
            .env(FLUX_SYSROOT, &config.dst)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::piped())
            .output();

        match result {
            Ok(output) if output.status.success() => {
                eprintln!("OK");
                successes += 1;
            }
            Ok(output) => {
                eprintln!("ERROR");
                let stderr = String::from_utf8_lossy(&output.stderr).to_string();
                failures.push((test_path.clone(), stderr));
            }
            Err(e) => {
                eprintln!("ERROR");
                failures.push((test_path.clone(), e.to_string()));
            }
        }
    }

    // Print summary
    eprintln!();
    eprintln!("{}", "=".repeat(60));
    eprintln!("SUMMARY");
    eprintln!("{}", "=".repeat(60));
    eprintln!("Total tests run: {}", test_files.len());
    eprintln!("Passed: {}", successes);
    eprintln!("Failed: {}", failures.len());

    if !failures.is_empty() {
        eprintln!();
        eprintln!("Failed tests:");
        for (path, _) in &failures {
            let rel_path = path.strip_prefix(&pos_path).unwrap_or(path);
            eprintln!("  - {}", rel_path.display());
        }
        eprintln!("{}", "=".repeat(60));
        return Err(anyhow!("{} test(s) failed", failures.len()));
    }

    eprintln!("{}", "=".repeat(60));
    Ok(())
}

fn run(args: Run, rust_fixpoint: bool) -> anyhow::Result<()> {
    let libs = if args.no_extern_specs { &[FluxLib::FluxRs] } else { FluxLib::ALL };
    run_inner(
        args.input,
        BuildLibs { force: false, libs },
        ["-Ztrack-diagnostics=y".to_string()]
            .into_iter()
            .chain(args.opts),
        rust_fixpoint,
    )?;
    Ok(())
}

fn expand(args: Expand) -> Result<(), anyhow::Error> {
    run_inner(
        args.input,
        BuildLibs { force: false, libs: &[FluxLib::FluxRs] },
        ["-Zunpretty=expanded".to_string()],
        false,
    )?;
    Ok(())
}

fn run_inner(
    input: PathBuf,
    build_libs: BuildLibs,
    flags: impl IntoIterator<Item = String>,
    rust_fixpoint: bool,
) -> Result<(), anyhow::Error> {
    let config = SysrootConfig {
        profile: Profile::Dev,
        rust_fixpoint,
        dst: local_sysroot_dir()?,
        build_libs,
        bundle_solvers: false,
    };

    let flux_driver = install_sysroot(&config)?;

    let mut rustc_flags = default_flags(&config.dst, SysrootManifest::extern_args(&config.dst));
    rustc_flags.extend(flags);

    Command::new(flux_driver)
        .args(&rustc_flags)
        .arg(&input)
        .env(FLUX_SYSROOT, &config.dst)
        .run()
}

fn install(args: &Install, rust_fixpoint: bool) -> anyhow::Result<()> {
    let libs = if args.no_extern_specs { &[FluxLib::FluxRs] } else { FluxLib::ALL };
    let config = SysrootConfig {
        profile: args.profile(),
        rust_fixpoint,
        dst: default_flux_sysroot_dir(),
        build_libs: BuildLibs { force: false, libs },
        bundle_solvers: args.bundle_solvers,
    };
    install_sysroot(&config)?;
    link_binaries(&config.dst)
}

fn uninstall() -> anyhow::Result<()> {
    let sysroot = default_flux_sysroot_dir();
    for link in binary_links()? {
        if is_link_to(&link, &sysroot) {
            eprintln!("$ rm {}", link.display());
            remove_path(&link)?;
        }
    }
    eprintln!("$ rm -rf {}", sysroot.display());
    remove_path(&sysroot)?;
    Ok(())
}

/// Binaries in the sysroot that are linked from cargo's `bin` directory, which is where cargo looks
/// for external subcommands and is usually on the `PATH`.
const LINKED_BINARIES: &[&str] = &["cargo-flux", "flux"];

/// Returns the paths in cargo's `bin` directory the [`LINKED_BINARIES`] are linked from.
fn binary_links() -> anyhow::Result<Vec<PathBuf>> {
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
fn link_binaries(sysroot: &Path) -> anyhow::Result<()> {
    for (name, link) in LINKED_BINARIES.iter().zip(binary_links()?) {
        if let Some(parent) = link.parent() {
            create_dir(parent)?;
        }
        // Create the link next to its final location and rename it there, so it's replaced
        // atomically.
        let tmp = sibling_path(&link, "tmp");
        remove_path(&tmp)?;
        symlink_or_copy(&bin_path(sysroot, name), &tmp)?;
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

fn doc(_args: Doc) -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["doc", "--workspace", "--document-private-items", "--no-deps"])
        .env("RUSTDOCFLAGS", "-Zunstable-options --enable-index-page")
        .run()?;
    Ok(())
}

fn blick(args: &Blick) -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["run", "--package", "blick"])
        .arg("--")
        .args_if_some(args.port, |port| ["--port".to_string(), port.to_string()])
        // the regression tests, to open in the page
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/tests"))
        .run()
}

fn build_binary(bin: &str, profile: Profile, rust_fixpoint: bool) -> anyhow::Result<Utf8PathBuf> {
    Command::new("cargo")
        .args(["build", "--bin", bin, "--profile", profile.as_str()])
        .args_if(rust_fixpoint, ["--features", "rust-fixpoint"])
        .run_with_cargo_metadata()?
        .into_iter()
        .find(|artifact| artifact.target.name == bin && artifact.target.is_kind(TargetKind::Bin))
        .and_then(|artifact| artifact.executable)
        .ok_or_else(|| anyhow!("cannot find binary: `{bin}`"))
}

struct SysrootConfig {
    /// Profile used to build `flux-driver` and libraries
    profile: Profile,
    /// Whether rust-fixpoint should be enabled to build `flux-driver`
    rust_fixpoint: bool,
    /// Destination path for sysroot artifacts
    dst: PathBuf,
    build_libs: BuildLibs,
    /// Whether to download prebuilt solvers into the sysroot
    bundle_solvers: bool,
}

struct BuildLibs {
    /// If true, forces a clean build.
    force: bool,
    /// List of libraries to install
    libs: &'static [FluxLib],
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy)]
enum FluxLib {
    FluxAlloc,
    FluxAttrs,
    FluxCore,
    FluxRs,
}

impl FluxLib {
    const ALL: &[FluxLib] = &[Self::FluxAlloc, Self::FluxAttrs, Self::FluxCore, Self::FluxRs];

    const _ASSERT_ALL: () = { assert!(Self::ALL.len() == variant_count::<Self>()) };

    const fn package_name(self) -> &'static str {
        match self {
            FluxLib::FluxAlloc => "flux-alloc",
            FluxLib::FluxAttrs => "flux-attrs",
            FluxLib::FluxCore => "flux-core",
            FluxLib::FluxRs => "flux-rs",
        }
    }

    const fn target_name(self) -> &'static str {
        match self {
            FluxLib::FluxAlloc => "flux_alloc",
            FluxLib::FluxAttrs => "flux_attrs",
            FluxLib::FluxCore => "flux_core",
            FluxLib::FluxRs => "flux_rs",
        }
    }

    /// Whether this lib's specs are injected as force externs under `-Fstd-extern-specs`.
    const fn is_std_extern_spec(self) -> bool {
        match self {
            FluxLib::FluxCore | FluxLib::FluxAlloc => true,
            FluxLib::FluxAttrs | FluxLib::FluxRs => false,
        }
    }

    fn from_artifact(artifact: &Artifact) -> Option<FluxLib> {
        Self::ALL
            .iter()
            .copied()
            .find(|lib| artifact.target.name == lib.target_name())
    }
}

/// Builds the sysroot in a staging directory next to `config.dst` and then replaces `config.dst`
/// with it, so a failed build leaves the existing sysroot untouched.
fn install_sysroot(config: &SysrootConfig) -> anyhow::Result<Utf8PathBuf> {
    let staging = sibling_path(&config.dst, "new");
    remove_path(&staging)?;
    create_dir(&bin_dir(&staging))?;
    create_dir(&lib_dir(&staging))?;

    let flux_driver = build_binary("flux-driver", config.profile, config.rust_fixpoint)?;
    copy_file(&flux_driver, bin_path(&staging, "flux-driver"))?;

    // The libraries are built with `cargo-flux` using the staging sysroot, which needs a valid
    // manifest to find the toolchain. Write one without crates now and add them once built.
    let mut manifest = SysrootManifest {
        toolchain: rust_toolchain()?,
        version: flux_version(),
        crates: BTreeMap::new(),
    };
    write_sysroot_toml(&manifest, &staging)?;

    let cargo_flux = build_binary("cargo-flux", config.profile, config.rust_fixpoint)?;
    copy_file(&cargo_flux, bin_path(&staging, "cargo-flux"))?;
    let flux = build_binary("flux", config.profile, config.rust_fixpoint)?;
    copy_file(&flux, bin_path(&staging, "flux"))?;

    if config.build_libs.force {
        Command::new(&cargo_flux)
            .args(["flux", "clean"])
            .env(FLUX_SYSROOT, &staging)
            .run()?;
    }
    let artifacts = Command::new(&cargo_flux)
        .args(["flux", "build"])
        .args(
            config
                .build_libs
                .libs
                .iter()
                .flat_map(|lib| ["-p", lib.package_name()]),
        )
        .env(FLUX_SYSROOT, &staging)
        .run_with_cargo_metadata()?;
    manifest.crates = copy_artifacts(&artifacts, &lib_dir(&staging))?;
    write_sysroot_toml(&manifest, &staging)?;

    if config.bundle_solvers {
        solvers::bundle(&bin_dir(&staging))?;
    }

    replace_dir(&staging, &config.dst)?;
    Ok(flux_driver)
}

/// Replaces `dst` with `src`. Where the platform and filesystem support it, the two are exchanged
/// atomically. Elsewhere (e.g., on Windows), `dst` is moved out of the way first, so it briefly
/// doesn't exist.
fn replace_dir(src: &Path, dst: &Path) -> anyhow::Result<()> {
    if !dst.exists() {
        return rename(src, dst);
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        use rustix::fs::{renameat_with, RenameFlags, CWD};
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

fn rename(src: &Path, dst: &Path) -> anyhow::Result<()> {
    eprintln!("$ mv {} {}", src.display(), dst.display());
    fs::rename(src, dst).map_err(|err| {
        anyhow!("failed to rename `{}` to `{}`: {err}", src.display(), dst.display())
    })
}

/// Returns `path` with `.{suffix}` appended, e.g., `sysroot` becomes `sysroot.new`.
fn sibling_path(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{suffix}"));
    path.with_file_name(name)
}

/// Version of the Flux sources, read from git when the sysroot is built.
fn flux_version() -> FluxVersion {
    FluxVersion {
        sha: git(&["describe", "--always", "--dirty=*"]),
        sha_full: git(&["describe", "--always", "--abbrev=0", "--dirty=*"]),
        date: git(&["show", "-s", "--format=%cd", "--date=format:%Y-%m-%d", "HEAD"]),
    }
}

/// Rust toolchain used to build the sysroot. When xtask runs through rustup, `RUSTUP_TOOLCHAIN`
/// holds the active toolchain, whether it comes from `+toolchain` or `rust-toolchain.toml`.
/// Otherwise, it's the one in `rust-toolchain.toml`.
fn rust_toolchain() -> anyhow::Result<String> {
    if let Ok(toolchain) = env::var("RUSTUP_TOOLCHAIN") {
        return Ok(toolchain);
    }
    let path = workspace_root().join("rust-toolchain.toml");
    let content = fs::read_to_string(&path)
        .map_err(|err| anyhow!("failed to read `{}`: {err}", path.display()))?;
    Ok(parse_toolchain_file(&content)?)
}

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
}

/// Runs git in the workspace root and returns its trimmed output, or `unknown` if it fails.
fn git(args: &[&str]) -> String {
    Command::new("git")
        .args(args)
        .current_dir(workspace_root())
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map_or_else(|| "unknown".to_string(), |stdout| stdout.trim().to_string())
}

fn copy_artifacts(
    artifacts: &[Artifact],
    lib_dir: &Path,
) -> anyhow::Result<BTreeMap<String, SysrootCrate>> {
    let mut crates = BTreeMap::<String, SysrootCrate>::new();
    for artifact in artifacts {
        let Some(lib) = FluxLib::from_artifact(artifact) else { continue };

        let entry = crates.entry(lib.target_name().to_string()).or_default();
        entry.extern_spec = lib.is_std_extern_spec();

        for filename in &artifact.filenames {
            copy_artifact(artifact, filename, lib_dir, entry)?;
        }
    }
    Ok(crates)
}

fn copy_artifact(
    artifact: &Artifact,
    filename: &Utf8Path,
    dst: &Path,
    entry: &mut SysrootCrate,
) -> anyhow::Result<()> {
    let name = sysroot_file_name(artifact, filename)?;
    copy_file(filename, dst.join(&name))?;
    record_artifact(entry, &name);

    if filename.extension() == Some("rmeta") {
        // Flux finds its own metadata by swapping the extension on the resolved `.rmeta` path,
        // so the two must travel together.
        let fluxmeta = filename.with_extension("fluxmeta");
        if fluxmeta.exists() {
            let name = sysroot_file_name(artifact, &fluxmeta)?;
            copy_file(&fluxmeta, dst.join(&name))?;
            record_artifact(entry, &name);
        }
    }
    Ok(())
}

fn record_artifact(entry: &mut SysrootCrate, name: &str) {
    let slot = match Utf8Path::new(name).extension() {
        Some("rlib") => &mut entry.rlib,
        Some("rmeta") => &mut entry.rmeta,
        Some("fluxmeta") => &mut entry.fluxmeta,
        // Proc macros are always built for the host. Anything else cargo reports, like `.pdb`
        // debug symbols on Windows, is not a crate.
        Some(extension) if extension == env::consts::DLL_EXTENSION => &mut entry.dylib,
        _ => return,
    };
    *slot = Some(name.to_string());
}

/// Name an artifact gets inside the sysroot.
///
/// Cargo reports an uplifted, hash-free `.rlib` for these crates but a hashed `.rmeta`, and rustc
/// pairs the two by the infix between `lib<crate>` and the extension, so we cannot reuse cargo's
/// names. Naming by crate keeps the pairing intact.
fn sysroot_file_name(artifact: &Artifact, filename: &Utf8Path) -> anyhow::Result<String> {
    let krate = &artifact.target.name;
    let name = filename
        .file_name()
        .ok_or_else(|| anyhow!("artifact `{filename}` has no file name"))?;
    let extension = filename
        .extension()
        .ok_or_else(|| anyhow!("artifact `{filename}` has no extension"))?;
    match extension {
        // rustc hardcodes the `lib` prefix for its own formats on every target.
        "rlib" | "rmeta" | "fluxmeta" => Ok(format!("lib{krate}.{extension}")),
        // A dylib's prefix is target-dependent (empty on Windows), so recover it from the name
        // cargo produced.
        _ => {
            let prefix = name
                .find(krate.as_str())
                .map(|idx| &name[..idx])
                .ok_or_else(|| anyhow!("artifact `{name}` does not mention crate `{krate}`"))?;
            Ok(format!("{prefix}{krate}.{extension}"))
        }
    }
}

fn write_sysroot_toml(manifest: &SysrootManifest, sysroot: &Path) -> anyhow::Result<()> {
    let content = toml::to_string(manifest)?;
    let path = sysroot.join(SYSROOT_MANIFEST);
    eprintln!("$ write {}", path.display());
    fs::write(&path, &content).map_err(|e| anyhow!("failed to write `{}`: {e}", path.display()))
}

impl Install {
    fn profile(&self) -> Profile {
        self.profile.unwrap_or(Profile::Release)
    }
}

fn local_sysroot_dir() -> anyhow::Result<PathBuf> {
    Ok(Path::new(file!())
        .canonicalize()?
        .ancestors()
        .nth(3)
        .unwrap()
        .join("sysroot"))
}

fn check_status(st: ExitStatus) -> anyhow::Result<()> {
    if st.success() {
        return Ok(());
    }
    let err = match st.code() {
        Some(code) => anyhow!("command exited with non-zero code: {code}"),
        #[cfg(unix)]
        None => {
            use std::os::unix::process::ExitStatusExt;
            match st.signal() {
                Some(sig) => anyhow!("command was terminated by a signal: {sig}"),
                None => anyhow!("command was terminated by a signal"),
            }
        }
        #[cfg(not(unix))]
        None => anyhow!("command was terminated by a signal"),
    };
    Err(err)
}

fn display_command(cmd: &Command) {
    for var in cmd.get_envs() {
        if let Some(val) = var.1 {
            eprintln!("$ export {}={}", var.0.display(), val.display());
        }
    }

    let prog = cmd.get_program();
    eprint!("$ {}", prog.display());
    for arg in cmd.get_args() {
        eprint!(" {}", arg.display());
    }
    eprintln!();
}

fn copy_file<S: AsRef<Path>, D: AsRef<Path>>(src: S, dst: D) -> anyhow::Result<()> {
    let src = src.as_ref();
    let dst = dst.as_ref();
    eprintln!("$ cp {} {}", src.display(), dst.display());

    let mut _tmp;
    let mut dst = dst;
    if dst.is_dir() {
        if let Some(file_name) = src.file_name() {
            _tmp = dst.join(file_name);
            dst = &_tmp;
        }
    }
    std::fs::copy(src, dst).map_err(|err| {
        anyhow!("failed to copy `{}` to `{}`: {err}", src.display(), dst.display())
    })?;

    Ok(())
}

trait CommandExt {
    fn run(&mut self) -> anyhow::Result<()>;
    fn run_with_cargo_metadata(&mut self) -> anyhow::Result<Vec<Artifact>>;
    /// Add `args` if `cond` is true.
    fn args_if<I, S>(&mut self, cond: bool, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>;
    /// If `opt` is `Some`, add the arguments computed by `f` from its value.
    fn args_if_some<T, I, S>(&mut self, opt: Option<T>, f: impl FnOnce(T) -> I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>;
}

impl CommandExt for Command {
    fn args_if<I, S>(&mut self, cond: bool, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        if cond {
            self.args(args);
        }
        self
    }

    fn args_if_some<T, I, S>(&mut self, opt: Option<T>, f: impl FnOnce(T) -> I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        if let Some(val) = opt {
            self.args(f(val));
        }
        self
    }

    fn run(&mut self) -> anyhow::Result<()> {
        display_command(self);
        let mut child = self.spawn()?;
        check_status(child.wait()?)
    }

    fn run_with_cargo_metadata(&mut self) -> anyhow::Result<Vec<Artifact>> {
        self.arg("--message-format=json-render-diagnostics")
            .stdout(std::process::Stdio::piped());

        display_command(self);

        let mut child = self.spawn()?;

        let mut artifacts = vec![];
        let reader = std::io::BufReader::new(child.stdout.take().unwrap());
        for message in cargo_metadata::Message::parse_stream(reader) {
            match message.unwrap() {
                Message::CompilerMessage(msg) => {
                    println!("{msg}");
                }
                Message::CompilerArtifact(artifact) => {
                    artifacts.push(artifact);
                }
                _ => (),
            }
        }

        check_status(child.wait()?)?;

        Ok(artifacts)
    }
}

/// Removes the file or directory at `path`. A symlink is removed itself, not what it points to.
fn remove_path(path: &Path) -> anyhow::Result<()> {
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
    std::fs::remove_dir_all(path)
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

fn create_dir(path: &Path) -> anyhow::Result<()> {
    match fs::create_dir_all(path) {
        Ok(()) => Ok(()),
        Err(err) => Err(anyhow!("failed to create directory `{}`: {err}", path.display())),
    }
}
