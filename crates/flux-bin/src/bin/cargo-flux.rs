#![feature(let_chains)]

use std::{
    self, env,
    io::{BufWriter, Write},
    process::{Command, exit},
};

use anyhow::anyhow;
use cargo_metadata::{Metadata, MetadataCommand};
use flux_bin::{
    FluxMetadata,
    utils::{
        EXIT_ERR, LIB_PATH, get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path,
        prepend_path_to_env_var, sysroot_dir,
    },
};
use itertools::Itertools;
use tempfile::NamedTempFile;

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("Failed to run `cargo-flux`, error={e}");
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> anyhow::Result<i32> {
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
        .arg("-Zprofile-rustflags")
        .arg("--config")
        .arg(config_file.path())
        .args(args)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}

fn write_cargo_config(toolchain: &str, metadata: Metadata) -> anyhow::Result<NamedTempFile> {
    let sysroot = sysroot_dir();
    let flux_driver_path = get_flux_driver_path(&sysroot)?;
    let ld_library_path = get_rustc_driver_lib_path(toolchain)?;
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

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
[build]
rustc = "{flux_driver}"

[env]
LIB_PATH = "{lib_path}"
FLUX_BUILD_SYSROOT = "1"
FLUX_CARGO = "1"

[profile.flux]
inherits = "dev"
incremental = false
        "#,
            flux_driver = flux_driver_path.display(),
            lib_path = extended_lib_path.display(),
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
                // members must be hierarchicaly bellow the workspace root, so the
                // following should never fail
                let manifest_dir_relative_to_workspace = package
                    .manifest_path
                    .strip_prefix(&metadata.workspace_root)?
                    .parent()
                    .ok_or_else(|| anyhow!("no parent for manifest file"))?;
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
        serde_json::Value::String(s) => config::ValueKind::String(s.to_string()),
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
                    .map(|(k, v)| Ok((k.to_string(), serde_json_to_config(v, origin)?)))
                    .try_collect()?,
            )
        }
    };
    Ok(config::Value::new(Some(origin), kind))
}
