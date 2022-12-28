mod logger;
use std::{env, io, process::exit};

const CMD_RUSTC: &str = "rustc";

fn main() -> io::Result<()> {
    logger::install()?;

    // HACK(nilehmann)
    // * Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument. We igore the
    //   argument and use it to determine if the binary is being called from cargo.
    // * Disable incremental compilation because that makes the borrow checker to not run
    //   and we fail to retrieve the mir.
    let mut args = vec![];
    let mut in_cargo = false;
    let mut is_codegen = false;
    for arg in env::args() {
        if arg.starts_with("-C") || arg.starts_with("--codegen") {
            is_codegen = true;
        } else if is_codegen && arg.starts_with("incremental=") {
            is_codegen = false;
        } else {
            if is_codegen {
                args.push("-C".to_string());
                is_codegen = false;
            }
            if arg == CMD_RUSTC {
                in_cargo = true;
            } else {
                args.push(arg);
            }
        }
    }
    let exit_code = flux_driver::run_compiler(args, in_cargo);
    // Exit with the exit code returned by the compiler.
    exit(exit_code)
}
