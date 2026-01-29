#![feature(variant_count)]

use std::{
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
use tests::{FLUX_SYSROOT, FLUX_SYSROOT_TEST};

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
            /// Do not check tests in Flux libs.
            optional --no-lib-tests
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
            /// Extra options to pass to the `flux` binary, e.g. `cargo x run file.rs -- -Zdump-mir=renumber`
            repeated opts: String
            /// Do not build Flux libs for extern specs
            optional --no-extern-specs
        }
        /// Expand Flux macros
        cmd expand {
            /// Input file
            required input: PathBuf
        }
        /// Install Flux binaries to `~/.cargo/bin` and precompiled libraries and driver to `~/.flux`
        cmd install {
            /// Select build profile for the `flux-driver`, either 'release', 'dev', or 'profiling'. Default 'release'
            optional --profile profile: Profile
            /// Do not install Flux libs or extern specs
            optional --no-extern-specs
        }
        /// Uninstall Flux binaries and libraries
        cmd uninstall { }
        /// Generate precompiled libraries
        cmd build-sysroot { }
        /// Build the documentation
        cmd doc { }
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
            println!("{}", Xtask::HELP_);
            if err.is_help() {
                std::process::exit(0);
            } else {
                println!("{}", Xtask::HELP_);
                std::process::exit(2);
            }
        }
    };

    let mut extra = vec![];
    if cmd.offline {
        extra.push("--offline");
    }
    match cmd.subcommand {
        XtaskCmd::Test(args) => test(args, cmd.rust_fixpoint),
        XtaskCmd::LeanBench(args) => lean_bench(args, cmd.rust_fixpoint),
        XtaskCmd::Run(args) => run(args, cmd.rust_fixpoint),
        XtaskCmd::Install(args) => install(&args, &extra, cmd.rust_fixpoint),
        XtaskCmd::Doc(args) => doc(args),
        XtaskCmd::BuildSysroot(_) => {
            let config = SysrootConfig {
                profile: Profile::Dev,
                rust_fixpoint: cmd.rust_fixpoint,
                dst: local_sysroot_dir()?,
                build_libs: BuildLibs { force: true, tests: true, libs: FluxLib::ALL },
            };
            install_sysroot(&config)?;
            Ok(())
        }
        XtaskCmd::Uninstall(_) => uninstall(),
        XtaskCmd::Expand(args) => expand(args),
    }
}

fn test(args: Test, rust_fixpoint: bool) -> anyhow::Result<()> {
    let config = SysrootConfig {
        profile: Profile::Dev,
        rust_fixpoint,
        dst: local_sysroot_dir()?,
        build_libs: BuildLibs { force: false, tests: !args.no_lib_tests, libs: FluxLib::ALL },
    };
    let flux = build_binary("flux", config.profile, false)?;
    install_sysroot(&config)?;

    Command::new("cargo")
        .args(["test", "-p", "tests", "--"])
        .args(["--flux", flux.as_str()])
        .args(["--sysroot".as_ref(), config.dst.as_os_str()])
        .map_opt(args.filter.as_ref(), |filter, cmd| {
            cmd.args(["--filter", filter]);
        })
        .run()
}

fn lean_bench(args: LeanBench, rust_fixpoint: bool) -> anyhow::Result<()> {
    use walkdir::WalkDir;

    let config = SysrootConfig {
        profile: Profile::Dev,
        rust_fixpoint,
        dst: local_sysroot_dir()?,
        build_libs: BuildLibs { force: false, tests: false, libs: FluxLib::ALL },
    };
    install_sysroot(&config)?;
    let flux = build_binary("flux", config.profile, false)?;

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
        let mut rustc_flags = tests::default_flags();
        rustc_flags.push("-Flean=emit".to_string());
        rustc_flags.push(format!("-Flean-dir={}", lean_dir.display()));

        // Run the test
        let result = Command::new(&flux)
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
        BuildLibs { force: false, tests: false, libs },
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
        BuildLibs { force: false, tests: false, libs: &[FluxLib::FluxRs] },
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
    };

    install_sysroot(&config)?;
    let flux = build_binary("flux", config.profile, false)?;

    let mut rustc_flags = tests::default_flags();
    rustc_flags.extend(flags);

    Command::new(flux)
        .args(&rustc_flags)
        .arg(&input)
        .env(FLUX_SYSROOT, &config.dst)
        .run()
}

fn install(args: &Install, extra: &[&str], rust_fixpoint: bool) -> anyhow::Result<()> {
    let libs = if args.no_extern_specs { &[FluxLib::FluxRs] } else { FluxLib::ALL };
    let config = SysrootConfig {
        profile: args.profile(),
        rust_fixpoint,
        dst: default_sysroot_dir(),
        build_libs: BuildLibs { force: false, tests: false, libs },
    };
    install_sysroot(&config)?;
    Command::new("cargo")
        .args(["install", "--path", "crates/flux-bin", "--force"])
        .args(extra)
        .run()
}

fn uninstall() -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["uninstall", "-p", "flux-bin"])
        .run()?;
    eprintln!("$ rm -rf ~/.flux");
    remove_path(&default_sysroot_dir())?;
    Ok(())
}

fn doc(_args: Doc) -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["doc", "--workspace", "--document-private-items", "--no-deps"])
        .env("RUSTDOCFLAGS", "-Zunstable-options --enable-index-page")
        .run()?;
    Ok(())
}

fn build_binary(bin: &str, profile: Profile, rust_fixpoint: bool) -> anyhow::Result<Utf8PathBuf> {
    let mut args = vec!["build", "--bin", bin, "--profile", profile.as_str()];
    if rust_fixpoint {
        args.extend_from_slice(&["--features", "rust-fixpoint"]);
    }
    Command::new("cargo")
        .args(&args)
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
}

struct BuildLibs {
    /// If true, forces a clean build.
    force: bool,
    /// If is true, run library tests.
    tests: bool,
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

    fn is_flux_lib(artifact: &Artifact) -> bool {
        Self::ALL
            .iter()
            .any(|lib| artifact.target.name == lib.target_name())
    }
}

fn install_sysroot(config: &SysrootConfig) -> anyhow::Result<()> {
    remove_path(&config.dst)?;
    create_dir(&config.dst)?;

    copy_file(build_binary("flux-driver", config.profile, config.rust_fixpoint)?, &config.dst)?;

    let cargo_flux = build_binary("cargo-flux", config.profile, config.rust_fixpoint)?;

    if config.build_libs.force {
        Command::new(&cargo_flux)
            .args(["flux", "clean"])
            .env(FLUX_SYSROOT, &config.dst)
            .run()?;
    }

    let artifacts = Command::new(cargo_flux)
        .arg("flux")
        .args(
            config
                .build_libs
                .libs
                .iter()
                .flat_map(|lib| ["-p", lib.package_name()]),
        )
        .env(FLUX_SYSROOT, &config.dst)
        .env_if(config.build_libs.tests, FLUX_SYSROOT_TEST, "1")
        .run_with_cargo_metadata()?;

    copy_artifacts(&artifacts, &config.dst)?;
    Ok(())
}

fn copy_artifacts(artifacts: &[Artifact], sysroot: &Path) -> anyhow::Result<()> {
    for artifact in artifacts {
        if !FluxLib::is_flux_lib(artifact) {
            continue;
        }

        for filename in &artifact.filenames {
            copy_artifact(filename, sysroot)?;
        }
    }
    Ok(())
}

fn copy_artifact(filename: &Utf8Path, dst: &Path) -> anyhow::Result<()> {
    copy_file(filename, dst)?;
    if filename.extension() == Some("rmeta") {
        let fluxmeta = filename.with_extension("fluxmeta");
        if fluxmeta.exists() {
            copy_file(&fluxmeta, dst)?;
        }
    }
    Ok(())
}

impl Install {
    fn profile(&self) -> Profile {
        self.profile.unwrap_or(Profile::Release)
    }
}

fn default_sysroot_dir() -> PathBuf {
    home::home_dir()
        .expect("Couldn't find home directory")
        .join(".flux")
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
    fn map_opt<T>(&mut self, b: Option<&T>, f: impl FnOnce(&T, &mut Self)) -> &mut Self;
    fn run(&mut self) -> anyhow::Result<()>;
    fn env_if<K, V>(&mut self, b: bool, k: K, v: V) -> &mut Self
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>;
    fn run_with_cargo_metadata(&mut self) -> anyhow::Result<Vec<Artifact>>;
}

impl CommandExt for Command {
    fn map_opt<T>(&mut self, opt: Option<&T>, f: impl FnOnce(&T, &mut Self)) -> &mut Self {
        if let Some(v) = opt {
            f(v, self);
        }
        self
    }

    fn env_if<K, V>(&mut self, b: bool, k: K, v: V) -> &mut Self
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        if b {
            self.env(k, v);
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

fn remove_path(path: &Path) -> anyhow::Result<()> {
    match path.metadata() {
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
