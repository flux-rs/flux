use std::{
    self, env,
    io::{BufWriter, Write},
    process::{Command, exit},
};

use anyhow::anyhow;
use cargo_metadata::{Metadata, camino::Utf8Path};
use clap::Parser as _;
use flux_bin::{
    FluxMetadata,
    cargo_flux_opts::{CargoFluxCommand, Cli},
    utils::{
        EXIT_ERR, flux_sysroot_dir, get_binary_path, get_flux_driver_path, get_rust_toolchain,
        get_version, get_version_full,
    },
};
use itertools::Itertools;
use tempfile::NamedTempFile;

fn main() {
    let Cli::Flux { check_opts, command, version, verbose } = Cli::parse();

    // Handle version flag (-V or --version)
    if version {
        if verbose {
            println!("cargo-flux {}", get_version_full());
        } else {
            println!("cargo-flux {}", get_version());
        }
        exit(0);
    }

    let command = command.unwrap_or(CargoFluxCommand::Check(check_opts));

    // Handle version subcommand
    if let CargoFluxCommand::Version { verbose } = command {
        if verbose {
            println!("cargo-flux {}", get_version_full());
        } else {
            println!("cargo-flux {}", get_version());
        }
        exit(0);
    }

    match run(command) {
        Ok(exit_code) => exit(exit_code),
        Err(e) => {
            println!("Failed to run `cargo-flux`, error={e}");
            exit(EXIT_ERR)
        }
    };
}

fn run(cargo_flux_cmd: CargoFluxCommand) -> anyhow::Result<i32> {
    let toolchain = get_rust_toolchain()?;
    let cargo_path = get_binary_path(&toolchain, "cargo")?;

    let metadata = cargo_flux_cmd.metadata().cargo_path(&cargo_path).exec()?;
    let config_file = write_cargo_config(metadata)?;

    let sysroot = flux_sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&sysroot)?;

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

fn write_cargo_config(metadata: Metadata) -> anyhow::Result<NamedTempFile> {
    let flux_flags: Option<Vec<String>> = if let Ok(flags) = env::var("FLUXFLAGS") {
        Some(flags.split(" ").map(Into::into).collect())
    } else {
        None
    };

    let flux_toml = config::Config::builder()
        .add_source(config::File::with_name("flux.toml").required(false))
        .build()?;

    if flux_toml.get_bool("enabled").is_ok() {
        return Err(anyhow!("`enabled` cannot be set in `flux.toml`"));
    }

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

        for package in metadata.packages {
            let flux_metadata: FluxMetadata = config::Config::builder()
                .add_source(FluxMetadataSource::new(
                    package.manifest_path.to_string(),
                    package.metadata,
                ))
                .add_source(flux_toml.clone())
                .build()?
                .try_deserialize()?;

            if flux_metadata.enabled {
                // For workspace members, cargo sets the workspace's root as the working dir
                // when running flux. Paths will be relative to that, so we must normalize
                // glob patterns to be relative to the workspace's root.
                let manifest_dir_relative_to_workspace = package
                    .manifest_path
                    .strip_prefix(&metadata.workspace_root)
                    .ok()
                    .and_then(Utf8Path::parent);
                write!(
                    w,
                    r#"
[profile.flux.package."{}"]
rustflags = [{:?}]
                        "#,
                    package.id,
                    flux_metadata
                        .into_flags(&metadata.target_directory, manifest_dir_relative_to_workspace)
                        .iter()
                        .chain(flux_flags.iter().flatten())
                        .map(|s| s.as_ref())
                        .chain(["-Fverify=on", "-Ffull-compilation=on"])
                        .format(", ")
                )?;
            }
        }
    }
    Ok(file)
}

#[derive(Clone, Debug)]
struct FluxMetadataSource {
    origin: String,
    value: serde_json::Value,
}

impl FluxMetadataSource {
    fn new(origin: String, value: serde_json::Value) -> Self {
        Self { origin, value }
    }
}

impl config::Source for FluxMetadataSource {
    fn clone_into_box(&self) -> Box<dyn config::Source + Send + Sync> {
        Box::new(self.clone())
    }

    fn collect(&self) -> Result<config::Map<String, config::Value>, config::ConfigError> {
        if let serde_json::Value::Object(metadata) = &self.value
            && let Some(flux_metadata) = metadata.get("flux")
        {
            let config_value = serde_json_to_config(flux_metadata, &self.origin)?;
            if let config::ValueKind::Table(table) = config_value.kind {
                Ok(table)
            } else {
                Err(config::ConfigError::Message("expected a table".to_string()))
            }
        } else {
            Ok(Default::default())
        }
    }
}

fn serde_json_to_config(
    value: &serde_json::Value,
    origin: &String,
) -> Result<config::Value, config::ConfigError> {
    let kind = match value {
        serde_json::Value::Null => config::ValueKind::Nil,
        serde_json::Value::Bool(b) => config::ValueKind::Boolean(*b),
        serde_json::Value::Number(number) => {
            if let Some(n) = number.as_u128() {
                config::ValueKind::U128(n)
            } else if let Some(n) = number.as_i128() {
                config::ValueKind::I128(n)
            } else if let Some(n) = number.as_u64() {
                config::ValueKind::U64(n)
            } else if let Some(n) = number.as_i64() {
                config::ValueKind::I64(n)
            } else if let Some(n) = number.as_f64() {
                config::ValueKind::Float(n)
            } else {
                return Err(config::ConfigError::Message("invalid number".to_string()));
            }
        }
        serde_json::Value::String(s) => config::ValueKind::String(s.clone()),
        serde_json::Value::Array(values) => {
            config::ValueKind::Array(
                values
                    .iter()
                    .map(|v| serde_json_to_config(v, origin))
                    .try_collect()?,
            )
        }
        serde_json::Value::Object(map) => {
            config::ValueKind::Table(
                map.iter()
                    .map(|(k, v)| Ok((k.clone(), serde_json_to_config(v, origin)?)))
                    .try_collect()?,
            )
        }
    };
    Ok(config::Value::new(Some(origin), kind))
}
