use std::path::PathBuf;

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
    match cmd.subcommand {
        XtaskCmd::Test(args) => test(sh, args),
        XtaskCmd::Run(args) => run(sh, args),
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
    let Run { input } = args;
    let flux_path = find_flux_path();
    let mut rustc_flags = rustc_flags();
    rustc_flags.extend([
        "-Zcrate-attr=feature(register_tool,custom_inner_attributes)".to_string(),
        "-Zcrate-attr=register_tool(flux)".to_string(),
        "-Ztrack-diagnostics=y".to_string(),
    ]);

    cmd!(sh, "cargo build").run()?;
    cmd!(sh, "{flux_path} {rustc_flags...} {input}").run()?;
    Ok(())
}
