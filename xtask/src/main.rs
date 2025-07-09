use std::{
    env,
    ffi::OsStr,
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
};

use anyhow::anyhow;
use cargo_metadata::{
    camino::{Utf8Path, Utf8PathBuf},
    Artifact, Message, TargetKind,
};
use tests::{FLUX_SYSROOT, FLUX_SYSROOT_TEST};
use xshell::{cmd, Shell};

xflags::xflags! {
    cmd xtask {
        /// If true, run all cargo commands with `--offline`
        optional --offline

        /// Run regression tests
        cmd test {
            /// Only run tests containing `filter` as a substring.
            optional filter: String
            /// Do not check tests in Flux libs.
            optional --no-lib-tests
        }
        /// Run the `flux` binary on the given input file.
        cmd run {
            /// Input file
            required input: PathBuf
            /// Extra options to pass to the `flux` binary, e.g. `cargo x run file.rs -- -Zdump-mir=y`
            repeated opts: String
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
            /// Do not build Flux libs
            optional --no-libs
        }
        /// Uninstall Flux binaries and libraries
        cmd uninstall { }
        /// Generate precompiled libraries
        cmd build-sysroot { }
        /// Build the documentation
        cmd doc {
            optional -o,--open
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
            println!("{}", Xtask::HELP_);
            if err.is_help() {
                std::process::exit(0);
            } else {
                println!("{}", Xtask::HELP_);
                std::process::exit(2);
            }
        }
    };

    let sh = Shell::new()?;
    sh.change_dir(project_root());

    let mut extra = vec![];
    if cmd.offline {
        extra.push("--offline");
    }
    match cmd.subcommand {
        XtaskCmd::Test(args) => test(sh, args),
        XtaskCmd::Run(args) => run(sh, args),
        XtaskCmd::Install(args) => install(&sh, &args, &extra),
        XtaskCmd::Doc(args) => doc(args),
        XtaskCmd::BuildSysroot(_) => {
            let config = SysrootConfig {
                profile: Profile::Dev,
                dst: local_sysroot_dir()?,
                build_libs: BuildLibs::Yes { force: true, tests: true },
            };
            install_sysroot(&sh, &config)?;
            Ok(())
        }
        XtaskCmd::Uninstall(_) => uninstall(&sh),
        XtaskCmd::Expand(args) => expand(&sh, args),
    }
}

fn test(sh: Shell, args: Test) -> anyhow::Result<()> {
    let config = SysrootConfig {
        profile: Profile::Dev,
        dst: local_sysroot_dir()?,
        build_libs: BuildLibs::Yes { force: false, tests: !args.no_lib_tests },
    };
    let flux = build_binary("flux", config.profile)?;
    install_sysroot(&sh, &config)?;

    Command::new("cargo")
        .args(["test", "-p", "tests", "--"])
        .args(["--flux", flux.as_str()])
        .args(["--sysroot".as_ref(), config.dst.as_os_str()])
        .map_opt(args.filter.as_ref(), |filter, cmd| {
            cmd.args(["--filter", filter]);
        })
        .run()
}

fn run(sh: Shell, args: Run) -> anyhow::Result<()> {
    run_inner(
        &sh,
        args.input,
        ["-Ztrack-diagnostics=y".to_string()]
            .into_iter()
            .chain(args.opts),
    )?;
    Ok(())
}

fn expand(sh: &Shell, args: Expand) -> Result<(), anyhow::Error> {
    run_inner(sh, args.input, ["-Zunpretty=expanded".to_string()])?;
    Ok(())
}

fn run_inner(
    sh: &Shell,
    input: PathBuf,
    flags: impl IntoIterator<Item = String>,
) -> Result<(), anyhow::Error> {
    let config = SysrootConfig {
        profile: Profile::Dev,
        dst: local_sysroot_dir()?,
        build_libs: BuildLibs::Yes { force: false, tests: false },
    };

    install_sysroot(sh, &config)?;
    let flux = build_binary("flux", config.profile)?;

    let mut rustc_flags = tests::default_flags();
    rustc_flags.extend(flags);

    Command::new(flux)
        .args(&rustc_flags)
        .arg(&input)
        .env(FLUX_SYSROOT, &config.dst)
        .run()
}

fn install(sh: &Shell, args: &Install, extra: &[&str]) -> anyhow::Result<()> {
    let config = SysrootConfig {
        profile: args.profile(),
        dst: default_sysroot_dir(),
        build_libs: if args.no_libs {
            BuildLibs::No
        } else {
            BuildLibs::Yes { force: false, tests: false }
        },
    };
    install_sysroot(sh, &config)?;
    Command::new("cargo")
        .args(["install", "--path", "crates/flux-bin", "--force"])
        .args(extra)
        .run()
}

fn uninstall(sh: &Shell) -> anyhow::Result<()> {
    cmd!(sh, "cargo uninstall -p flux-bin").run()?;
    eprintln!("$ rm -rf ~/.flux");
    sh.remove_path(default_sysroot_dir())?;
    Ok(())
}

fn doc(args: Doc) -> anyhow::Result<()> {
    Command::new("cargo")
        .args(["doc", "--workspace", "--document-private-items", "--no-deps"])
        .env("RUSTDOCFLAGS", "-Zunstable-options --enable-index-page")
        .run()?;
    if args.open {
        opener::open("target/doc/index.html")?;
    }
    Ok(())
}

fn project_root() -> PathBuf {
    Path::new(
        &env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| env!("CARGO_MANIFEST_DIR").to_owned()),
    )
    .ancestors()
    .nth(1)
    .unwrap()
    .to_path_buf()
}

fn build_binary(bin: &str, profile: Profile) -> anyhow::Result<Utf8PathBuf> {
    Command::new("cargo")
        .args(["build", "--bin", bin, "--profile", profile.as_str()])
        .run_with_cargo_metadata()?
        .into_iter()
        .find(|artifact| artifact.target.name == bin && artifact.target.is_kind(TargetKind::Bin))
        .and_then(|artifact| artifact.executable)
        .ok_or_else(|| anyhow!("cannot find binary: `{bin}`"))
}

struct SysrootConfig {
    /// Profile used to build `flux-driver` and libraries
    profile: Profile,
    /// Destination path for sysroot artifacts
    dst: PathBuf,
    build_libs: BuildLibs,
}

/// Whether to build Flux's libs
enum BuildLibs {
    /// If `force` is true, forces a clean build. If `tests` is true, check library tests.
    Yes { force: bool, tests: bool },
    /// Do not build libs
    No,
}

fn install_sysroot(sh: &Shell, config: &SysrootConfig) -> anyhow::Result<()> {
    sh.remove_path(&config.dst)?;
    sh.create_dir(&config.dst)?;

    copy_file(sh, build_binary("flux-driver", config.profile)?, &config.dst)?;

    let cargo_flux = build_binary("cargo-flux", config.profile)?;

    if let BuildLibs::Yes { force, tests } = config.build_libs {
        if force {
            Command::new(&cargo_flux)
                .args(["flux", "clean"])
                .env(FLUX_SYSROOT, &config.dst)
                .run()?;
        }

        let artifacts = Command::new(cargo_flux)
            .args(["flux", "-p", "flux-rs", "-p", "flux-core", "-p", "flux-alloc"])
            .env(FLUX_SYSROOT, &config.dst)
            .env_if(tests, FLUX_SYSROOT_TEST, "1")
            .run_with_cargo_metadata()?;

        copy_artifacts(sh, &artifacts, &config.dst)?;
    }
    Ok(())
}

fn copy_artifacts(sh: &Shell, artifacts: &[Artifact], sysroot: &Path) -> anyhow::Result<()> {
    for artifact in artifacts {
        if !is_flux_lib(artifact) {
            continue;
        }

        for filename in &artifact.filenames {
            copy_artifact(sh, filename, sysroot)?;
        }
    }
    Ok(())
}

fn copy_artifact(sh: &Shell, filename: &Utf8Path, dst: &Path) -> anyhow::Result<()> {
    copy_file(sh, filename, dst)?;
    if filename.extension() == Some("rmeta") {
        let fluxmeta = filename.with_extension("fluxmeta");
        if sh.path_exists(&fluxmeta) {
            copy_file(sh, &fluxmeta, dst)?;
        }
    }
    Ok(())
}

fn is_flux_lib(artifact: &Artifact) -> bool {
    matches!(&artifact.target.name[..], "flux_rs" | "flux_attrs" | "flux_core" | "flux_alloc")
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
            eprintln!("$ export {}={}", var.0.to_string_lossy(), val.to_string_lossy());
        }
    }

    let prog = cmd.get_program();
    eprint!("$ {}", prog.to_string_lossy());
    for arg in cmd.get_args() {
        eprint!(" {}", arg.to_string_lossy());
    }
    eprintln!();
}

fn copy_file<S: AsRef<Path>, D: AsRef<Path>>(sh: &Shell, src: S, dst: D) -> anyhow::Result<()> {
    let src = src.as_ref();
    let dst = dst.as_ref();
    eprintln!("$ cp {} {}", src.to_string_lossy(), dst.to_string_lossy());
    sh.copy_file(src, dst)?;
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
