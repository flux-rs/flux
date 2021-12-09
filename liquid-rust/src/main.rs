use std::{env::args, process::exit};

const CMD_PREFIX: &str = "-L";

fn main() {
    // Get the arguments from the command line.
    let args: Vec<String> = args().filter(|x| !x.starts_with(CMD_PREFIX)).collect();

    let exit_code = liquid_rust_driver::run_compiler(args);
    // Exit with the exit code returned by the compiler.
    exit(exit_code)
}
