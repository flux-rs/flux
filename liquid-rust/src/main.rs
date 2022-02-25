mod logger;
use std::{env::args, io, process::exit};

const CMD_PREFIX: &str = "-lr";

fn main() -> io::Result<()> {
    logger::install()?;
    let args: Vec<String> = args().filter(|x| !x.starts_with(CMD_PREFIX)).collect();

    let exit_code = liquid_rust_driver::run_compiler(args);
    // Exit with the exit code returned by the compiler.
    exit(exit_code)
}
