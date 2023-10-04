use std::{
    env,
    ffi::OsString,
    path::{Path, PathBuf},
};

use flux_tests::{find_flux_path, rustc_flags};
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
            repeated opts: OsString
        }
        /// Install flux binaries to ~/.cargo/bin
        cmd install {
            /// Build the flux-driver binary in debug mode (with the 'dev' profile) instead of release mode
            optional --debug
        }
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
                println!("{err}");
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
        XtaskCmd::Install(args) => install(sh, args),
        XtaskCmd::Doc(args) => doc(sh, args),
    }
}

fn test(sh: Shell, args: Test) -> anyhow::Result<()> {
    let Test { filter } = args;
    cmd!(sh, "cargo build").run()?;

    if let Some(filter) = filter {
        cmd!(sh, "cargo test -p flux-tests -- --test-args {filter}").run()?;
    } else {
        cmd!(sh, "cargo test -p flux-tests").run()?;
    }
    Ok(())
}

fn run(sh: Shell, args: Run) -> anyhow::Result<()> {
    let Run { input, opts } = args;
    cmd!(sh, "cargo build").run()?;

    let flux_path = find_flux_path();
    let mut rustc_flags = rustc_flags();
    rustc_flags.extend(["-Ztrack-diagnostics=y".to_string()]);

    cmd!(sh, "{flux_path} {rustc_flags...} {opts...} {input}").run()?;
    Ok(())
}

fn install(sh: Shell, args: Install) -> anyhow::Result<()> {
    let Install { debug } = args;
    let mut opts = vec!["--force"];
    if debug {
        opts.push("--debug");
    }
    cmd!(sh, "cargo install --path crates/flux-driver {opts...}").run()?;
    cmd!(sh, "cargo install --path crates/flux-bin --force").run()?;
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
