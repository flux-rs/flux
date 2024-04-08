use std::{
    env,
    path::{Path, PathBuf},
};

use flux_tests::{find_flux_path, FLUX_SYSROOT};
use xshell::{cmd, Shell};

xflags::xflags! {
    cmd xtask {
        /// Run regression tests
        cmd test {
            /// Only run tests containing `filter` as substring.
            optional filter: String
        }
        /// Run the flux binary on the given input file setting the appropriate flags to use
        /// custom flux attributes and macros.
        cmd run {
            /// Input file
            required input: PathBuf
            /// Extra options to pass to the flux binary, e.g. `cargo xtask run file.rs -- -Zdump-mir=y`
            repeated opts: String
        }
        /// Expand flux macros
        cmd expand {
            /// Input file
            required input: PathBuf
        }
        /// Install flux binaries to ~/.cargo/bin and precompiled libraries and driver to ~/.flux
        cmd install {
            /// Build the flux-driver binary in debug mode (with the 'dev' profile) instead of release mode
            optional --debug
        }
        /// Uninstall flux binaries and libraries
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
    match cmd.subcommand {
        XtaskCmd::Test(args) => test(sh, args),
        XtaskCmd::Run(args) => run(sh, args),
        XtaskCmd::Install(args) => install(&sh, &args),
        XtaskCmd::Doc(args) => doc(sh, args),
        XtaskCmd::BuildSysroot(_) => build_sysroot(&sh),
        XtaskCmd::Uninstall(_) => uninstall(&sh),
        XtaskCmd::Expand(args) => expand(&sh, args),
    }
}

fn prepare(sh: &Shell) -> Result<(), anyhow::Error> {
    build_sysroot(sh)?;
    cmd!(sh, "cargo build").run()?;
    Ok(())
}

fn test(sh: Shell, args: Test) -> anyhow::Result<()> {
    let Test { filter } = args;
    prepare(&sh)?;
    if let Some(filter) = filter {
        cmd!(sh, "cargo test -p flux-tests -- --test-args {filter}").run()?;
    } else {
        cmd!(sh, "cargo test -p flux-tests").run()?;
    }
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
    prepare(sh)?;
    let flux_path = find_flux_path();
    let _env = sh.push_env(FLUX_SYSROOT, flux_path.parent().unwrap());
    let mut rustc_flags = flux_tests::rustc_flags();
    rustc_flags.extend(flags);

    cmd!(sh, "{flux_path} {rustc_flags...} {input}").run()?;
    Ok(())
}

fn install(sh: &Shell, args: &Install) -> anyhow::Result<()> {
    cmd!(sh, "cargo install --path crates/flux-bin --force").run()?;
    install_driver(sh, args)?;
    install_libs(sh, args)?;

    Ok(())
}

fn install_driver(sh: &Shell, args: &Install) -> anyhow::Result<()> {
    let out_dir = default_sysroot_dir();
    if args.is_release() {
        cmd!(sh, "cargo build -Zunstable-options --bin flux-driver --release --out-dir {out_dir}")
            .run()?;
    } else {
        cmd!(sh, "cargo build -Zunstable-options --bin flux-driver --out-dir {out_dir}").run()?;
    }
    Ok(())
}

fn install_libs(sh: &Shell, args: &Install) -> anyhow::Result<()> {
    // CODESYNC(build-sysroot, 5)
    let _env = sh.push_env("FLUX_BUILD_SYSROOT", "1");

    let out_dir = default_sysroot_dir();
    if args.is_release() {
        cmd!(sh, "cargo build -Zunstable-options --release -p flux-rs --out-dir {out_dir}")
            .run()?;
    } else {
        cmd!(sh, "cargo build -Zunstable-options -p flux-rs --out-dir {out_dir}").run()?;
    }
    Ok(())
}

fn uninstall(sh: &Shell) -> anyhow::Result<()> {
    cmd!(sh, "cargo uninstall -p flux-bin").run()?;
    println!("$ rm -rf ~/.flux");
    std::fs::remove_dir_all(default_sysroot_dir())?;
    Ok(())
}

fn doc(sh: Shell, args: Doc) -> anyhow::Result<()> {
    let _env = sh.push_env("RUSTDOCFLAGS", "-Zunstable-options --enable-index-page");
    cmd!(sh, "cargo doc --document-private-items --no-deps").run()?;
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

fn build_sysroot(sh: &Shell) -> anyhow::Result<()> {
    // CODESYNC(build-sysroot, 5)
    let _env = sh.push_env("FLUX_BUILD_SYSROOT", "1");
    cmd!(sh, "cargo build -p flux-rs").run()?;
    Ok(())
}

impl Install {
    fn is_release(&self) -> bool {
        !self.debug
    }
}

// CODESYNC(default-sysroot) we must use the same default sysroot used in flux-bin
fn default_sysroot_dir() -> PathBuf {
    home::home_dir()
        .expect("Couldn't find home directory")
        .join(".flux")
}
