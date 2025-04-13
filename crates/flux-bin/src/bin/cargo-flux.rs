#![feature(let_chains, os_str_display)]

use std::{
    self, env,
    io::{BufWriter, Write},
    process::{Command, exit},
};

use anyhow::Result;
use cargo_metadata::{Metadata, MetadataCommand};
use flux_bin::utils::{
    EXIT_ERR, LIB_PATH, get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path,
    prepend_path_to_env_var, sysroot_dir,
};
use serde::Deserialize;
use tempfile::NamedTempFile;

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("Failed to run cargo-flux, error={e}");
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> Result<i32> {
    let toolchain = get_rust_toolchain()?;

    let metadata = MetadataCommand::new().exec()?;
    let config_file = write_cargo_config(&toolchain, metadata)?;

    // Cargo can be called like `cargo [OPTIONS] flux`, so we skip all arguments until `flux` is found.
    let mut args = env::args()
        .skip_while(|arg| arg != "flux")
        .skip(1)
        .collect::<Vec<_>>();

    // Unless we are calling `cargo flux clean` add a `check`
    match &args[..] {
        [subcommand, ..] if subcommand == "clean" => {}
        _ => {
            args.insert(0, "check".to_string());
        }
    }
    args.extend(["--profile".to_string(), "flux".to_string()]);

    let exit_code = Command::new("cargo")
        .arg(format!("+{toolchain}"))
        .arg("--config")
        .arg(config_file.path())
        .args(args)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}

#[derive(Deserialize, Debug, Default)]
#[serde(default)]
struct PackageMetadata {
    flux: Option<FluxMetadata>,
}

impl PackageMetadata {
    fn from_value(value: serde_json::Value) -> serde_json::Result<Self> {
        if value.is_null() { Ok(Self::default()) } else { serde_json::from_value(value) }
    }
}

#[derive(Deserialize, Debug)]
struct FluxMetadata {
    #[serde(default)]
    enabled: bool,
}

fn write_cargo_config(toolchain: &str, cargo_metadata: Metadata) -> Result<NamedTempFile> {
    let sysroot = sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&sysroot)?;
    let ld_library_path = get_rustc_driver_lib_path(toolchain)?;
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    let mut file = NamedTempFile::new()?;
    {
        let mut w = BufWriter::new(&mut file);
        write!(
            w,
            r#"
[build]
rustc = "{flux_driver}"

[profile.flux]
inherits = "dev"

[env]
LIB_PATH = "{lib_path}"
FLUX_BUILD_SYSROOT = "1"
FLUX_CARGO = "1"
        "#,
            flux_driver = flux_driver_path.display(),
            lib_path = extended_lib_path.display(),
        )?;

        for package in cargo_metadata.packages {
            let package_metadata = PackageMetadata::from_value(package.metadata)?;
            if let Some(flux_metadata) = package_metadata.flux
                && flux_metadata.enabled
            {
                write!(
                    w,
                    r#"
[profile.flux.package."{}"]
                    "#,
                    package.id
                )?;
            }
        }
    }
    Ok(file)
}
