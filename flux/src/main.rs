mod logger;
use std::{env::args, io, process::exit};

const CMD_PREFIX: &str = "-lr";
const CMD_RUSTC: &str = "rustc";

fn main() -> io::Result<()> {
    logger::install()?;

    // the extra != CMD_RUSTC is because the `rust-analyzer` plugin calls the `flux` binary
    // with that extra argument that we want stripped out...
    let args: Vec<String> = args()
        .filter(|x| !x.starts_with(CMD_PREFIX) && x != CMD_RUSTC)
        .collect();

    let exit_code = flux_driver::run_compiler(args);
    // Exit with the exit code returned by the compiler.
    exit(exit_code)
}
