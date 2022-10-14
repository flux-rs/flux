mod logger;
use std::{env::args, io, process::exit};

const CMD_PREFIX: &str = "-lr";
const CMD_RUSTC: &str = "rustc";

fn main() -> io::Result<()> {
    logger::install()?;

    // HACK(nilehmann) Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We igore the argument and use it to determine if the binary is being called from cargo.
    let mut in_cargo = false;
    let args: Vec<String> = args()
        .filter(|x| {
            in_cargo |= x == CMD_RUSTC;
            !x.starts_with(CMD_PREFIX) && x != CMD_RUSTC
        })
        .collect();

    let exit_code = flux_driver::run_compiler(args, in_cargo);
    // Exit with the exit code returned by the compiler.
    exit(exit_code)
}
