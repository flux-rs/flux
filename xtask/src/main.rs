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
use tests::FLUX_SYSROOT;
use xshell::{cmd, PushEnv, Shell};

xflags::xflags! {
    cmd xtask {
        optional --offline

        /// Run regression tests
        cmd test {
            /// Only run tests containing `filter` as substring.
            optional filter: String
        }
        /// Run the Flux binary on the given input file setting the appropriate flags to use
        /// custom Flux attributes and macros.
        cmd run {
            /// Input file
            required input: PathBuf
            /// Extra options to pass to the Flux binary, e.g. `cargo xtask run file.rs -- -Zdump-mir=y`
            repeated opts: String
        }
        /// Expand Flux macros
        cmd expand {
            /// Input file
            required input: PathBuf
        }
        /// Install Flux binaries to `~/.cargo/bin` and precompiled libraries and driver to `~/.flux`
        cmd install {
            /// Build the `flux-driver` binary in debug mode (with the 'dev' profile) instead of release mode
            optional --debug
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

fn main() -> anyhow::Result<()> {
    let cmd = match Xtask::from_env() {
        Ok(cmd) => cmd,
        Err(err) => {
            if err.is_help() {
                std::process::exit(0);
            } else {
                eprintln!("error: {err}\n");
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
        XtaskCmd::Doc(args) => doc(sh, args),
        XtaskCmd::BuildSysroot(_) => {
            install_sysroot(&sh, false, &local_sysroot_dir()?)?;
            Ok(())
        }
        XtaskCmd::Uninstall(_) => uninstall(&sh),
        XtaskCmd::Expand(args) => expand(&sh, args),
    }
}

fn test(sh: Shell, args: Test) -> anyhow::Result<()> {
    let sysroot = local_sysroot_dir()?;
    let Test { filter } = args;
    let flux = build_binary("flux", false)?;
    install_sysroot(&sh, false, &sysroot)?;

    let mut cmd = cmd!(sh, "cargo test -p tests -- --flux {flux} --sysroot {sysroot}");

    if let Some(filter) = &filter {
        cmd = cmd.args(["--filter", filter]);
    }
    cmd.run()?;

    Ok(())
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
    let sysroot = local_sysroot_dir()?;

    install_sysroot(sh, false, &sysroot)?;
    let flux = build_binary("flux", false)?;

    let _env = push_env(sh, FLUX_SYSROOT, &sysroot);
    let mut rustc_flags = tests::default_rustc_flags();
    rustc_flags.extend(flags);

    cmd!(sh, "{flux} {rustc_flags...} {input}").run()?;
    Ok(())
}

fn install(sh: &Shell, args: &Install, extra: &[&str]) -> anyhow::Result<()> {
    install_sysroot(sh, args.is_release(), &default_sysroot_dir())?;
    cmd!(sh, "cargo install --path crates/flux-bin --force {extra...}").run()?;
    Ok(())
}

fn uninstall(sh: &Shell) -> anyhow::Result<()> {
    cmd!(sh, "cargo uninstall -p flux-bin").run()?;
    eprintln!("$ rm -rf ~/.flux");
    sh.remove_path(default_sysroot_dir())?;
    Ok(())
}

fn doc(sh: Shell, args: Doc) -> anyhow::Result<()> {
    let _env = push_env(&sh, "RUSTDOCFLAGS", "-Zunstable-options --enable-index-page");
    cmd!(sh, "cargo doc --workspace --document-private-items --no-deps").run()?;
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

fn build_binary(bin: &str, release: bool) -> anyhow::Result<Utf8PathBuf> {
    Command::new("cargo")
        .args(["build", "--bin", bin])
        .arg_if(release, "--release")
        .run_with_cargo_metadata()?
        .into_iter()
        .find(|artifact| artifact.target.name == bin && artifact.target.is_kind(TargetKind::Bin))
        .and_then(|artifact| artifact.executable)
        .ok_or_else(|| anyhow!("cannot find binary: `{bin}`"))
}

fn install_sysroot(sh: &Shell, release: bool, sysroot: &Path) -> anyhow::Result<()> {
    sh.remove_path(sysroot)?;
    sh.create_dir(sysroot)?;

    copy_file(sh, build_binary("flux-driver", release)?, sysroot)?;

    let artifacts = Command::new(build_binary("cargo-flux", release)?)
        .args(["flux", "-p", "flux-rs", "-p", "flux-core"])
        .env(FLUX_SYSROOT, sysroot)
        .run_with_cargo_metadata()?;

    copy_artifacts(sh, &artifacts, sysroot)?;
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
    matches!(&artifact.target.name[..], "flux_rs" | "flux_attrs" | "flux_core")
}

impl Install {
    fn is_release(&self) -> bool {
        !self.debug
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

fn push_env<K: AsRef<OsStr>, V: AsRef<OsStr>>(sh: &Shell, key: K, val: V) -> PushEnv {
    let key = key.as_ref();
    let val = val.as_ref();
    eprintln!("$ export {}={}", key.to_string_lossy(), val.to_string_lossy());
    sh.push_env(key, val)
}

fn copy_file<S: AsRef<Path>, D: AsRef<Path>>(sh: &Shell, src: S, dst: D) -> anyhow::Result<()> {
    let src = src.as_ref();
    let dst = dst.as_ref();
    eprintln!("$ cp {} {}", src.to_string_lossy(), dst.to_string_lossy());
    sh.copy_file(src, dst)?;
    Ok(())
}

trait CommandExt {
    fn arg_if<S: AsRef<OsStr>>(&mut self, b: bool, arg: S) -> &mut Self;
    fn run_with_cargo_metadata(&mut self) -> anyhow::Result<Vec<Artifact>>;
}

impl CommandExt for Command {
    fn arg_if<S: AsRef<OsStr>>(&mut self, b: bool, arg: S) -> &mut Self {
        if b {
            self.arg(arg);
        }
        self
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
