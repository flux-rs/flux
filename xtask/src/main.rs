use xshell::{cmd, Shell};

xflags::xflags! {
    cmd xtask {
        /// Run regression tests
        cmd test {
            /// Only run tests containing `filter` as substring
            optional filter: String
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
