use std::process::exit;

use clap::Parser as _;
use flux_bin::{
    cargo_flux,
    cargo_flux_opts::{CargoFluxCommand, Cli},
    utils::{EXIT_ERR, print_version_and_exit},
};

fn main() {
    let Cli::Flux { check_opts, command, version, verbose } = Cli::parse();

    // Handle version flag (-V or --version with optional -v for verbose)
    if version {
        print_version_and_exit("cargo-flux", verbose > 0);
    }

    let command = command.unwrap_or(CargoFluxCommand::Check(check_opts));

    match cargo_flux::run(command) {
        Ok(exit_code) => exit(exit_code),
        Err(e) => {
            println!("Failed to run `cargo-flux`, error={e}");
            exit(EXIT_ERR)
        }
    }
}
