use std::{
    self,
    io::{BufWriter, Write},
    process::{Command, exit},
};

use cargo_metadata::{Metadata, camino::Utf8Path};
use clap::Parser as _;
use flux_bin::{
    FluxMetadata,
    cargo_flux_opts::{CargoFluxCommand, Cli},
    config::FluxConfig,
    utils::{
        EXIT_ERR, flux_sysroot_dir, get_binary_path, get_flux_driver_path, get_rust_toolchain,
        print_version_and_exit,
    },
};
use itertools::Itertools;
use tempfile::NamedTempFile;

fn main() {
    let Cli::Flux { check_opts, command, version, verbose } = Cli::parse();

    // Handle version flag (-V or --version with optional -v for verbose)
    if version {
        print_version_and_exit("cargo-flux", verbose > 0);
    }

    let command = command.unwrap_or(CargoFluxCommand::Check(check_opts));

    match run(command) {
        Ok(exit_code) => exit(exit_code),
        Err(e) => {
            println!("Failed to run `cargo-flux`, error={e:#}");
            exit(EXIT_ERR)
        }
    };
}

fn run(cargo_flux_cmd: CargoFluxCommand) -> anyhow::Result<i32> {
    let toolchain = get_rust_toolchain()?;
    let cargo_path = get_binary_path(&toolchain, "cargo")?;

    let metadata = cargo_flux_cmd.metadata().cargo_path(&cargo_path).exec()?;
    let sysroot = flux_sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&sysroot)?;
    let config_file = write_cargo_config(metadata, &sysroot, &cargo_flux_cmd)?;

    let mut cargo_command = Command::new("cargo");

    // We set `RUSTC` as an environment variable and not in in the [build]
    // section of the config file to make sure we run flux even when the
    // variable is already set. We also unset `RUSTC_WRAPPER` to avoid
    // conflicts, e.g., see https://github.com/flux-rs/flux/issues/1155
    cargo_command
        .env("RUSTC", flux_driver_path)
        .env("RUSTC_WRAPPER", "")
        .arg(format!("+{toolchain}"));

    cargo_flux_cmd.forward_args(&mut cargo_command, config_file.path());

    Ok(cargo_command.status()?.code().unwrap_or(EXIT_ERR))
}

fn write_cargo_config(
    metadata: Metadata,
    sysroot: &std::path::Path,
    cargo_flux_cmd: &CargoFluxCommand,
) -> anyhow::Result<NamedTempFile> {
    let flux_config = FluxConfig::load()?;
    let global_fluxflags = flux_config.global_fluxflags();
    let targeted_package_ids = cargo_flux_cmd.targeted_package_ids(&metadata);
    let cli_flags = cargo_flux_cmd.rustflags();

    let mut file = NamedTempFile::new()?;
    {
        let mut w = BufWriter::new(&mut file);
        write!(
            w,
            r#"
[unstable]
profile-rustflags = true

[env]
FLUX_BUILD_SYSROOT = "1"
FLUX_CARGO = "1"

[profile.flux]
inherits = "dev"
incremental = false
        "#
        )?;

        for package in &metadata.packages {
            let flux_metadata = FluxMetadata::from_package(package)?;

            if flux_metadata.enabled {
                // For workspace members, cargo sets the workspace's root as the working dir
                // when running flux. Paths will be relative to that, so we must normalize
                // glob patterns to be relative to the workspace's root.
                let manifest_dir_relative_to_workspace = package
                    .manifest_path
                    .strip_prefix(&metadata.workspace_root)
                    .ok()
                    .and_then(Utf8Path::parent);

                let sysroot_flag = format!("-Fsysroot={}", sysroot.display());
                write!(
                    w,
                    r#"
[profile.flux.package."{}"]
rustflags = [{:?}]
                        "#,
                    package.id,
                    // Like cargo's own flags before rustflags, the flags `cargo flux` sets itself
                    // come first, so any of them can be overridden.
                    ["-Fverify=on", "-Ffull-compilation=on", sysroot_flag.as_str()]
                        .into_iter()
                        .chain(
                            flux_metadata
                                .into_flags(
                                    manifest_dir_relative_to_workspace,
                                    cargo_flux_cmd
                                        .only_check()
                                        .filter(|_| targeted_package_ids.contains(&package.id))
                                )
                                .iter()
                                .chain(
                                    flux_config
                                        .settings
                                        .to_flags(&metadata.target_directory)
                                        .iter()
                                )
                                .chain(global_fluxflags.iter())
                                .chain(cli_flags.iter())
                                .map(String::as_str)
                        )
                        .format(", ")
                )?;
            }
        }
    }
    Ok(file)
}
