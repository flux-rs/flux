#![feature(let_chains, os_str_display)]

use std::{
    self, env,
    io::{BufWriter, Write},
    process::{Command, exit},
};

use cargo_metadata::{Metadata, MetadataCommand, camino::Utf8Path};
use flux_bin::utils::{
    EXIT_ERR, LIB_PATH, get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path,
    prepend_path_to_env_var, sysroot_dir,
};
use flux_config::SmtSolver;
use itertools::Itertools;
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

#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields)]
struct FluxMetadata {
    enabled: bool,
    cache: Option<bool>,
    solver: Option<SmtSolver>,
    scrape_quals: Option<bool>,
    check_overflow: Option<bool>,
    smt_define_fun: Option<bool>,
}

impl FluxMetadata {
    fn into_flags(self, target_dir: &Utf8Path) -> Vec<String> {
        let mut flags = vec![];
        if let Some(true) = self.cache {
            flags.push(format!("-Fcache={}", target_dir.join("FLUXCACHE")));
        }
        if let Some(v) = self.solver {
            flags.push(format!("-Fsolver={v}"));
        }
        if let Some(v) = self.check_overflow {
            flags.push(format!("-Fcheck-overflow={v}"));
        }
        if let Some(v) = self.scrape_quals {
            flags.push(format!("-Fscrape-quals={v}"));
        }
        if let Some(v) = self.smt_define_fun {
            flags.push(format!("-Fsmt-define-fun={v}"));
        }
        flags
    }
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

    let workspace_config = config::Config::builder()
        .add_source(config::File::with_name("flux.toml"))
        .build()?;

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
        "#,
            flux_driver = flux_driver_path.display(),
            lib_path = extended_lib_path.display(),
        )?;

        for package in metadata.packages {
            let flux_metadata: FluxMetadata = config::Config::builder()
                .add_source(workspace_config.clone())
                .add_source(FluxMetadataSource::new(package.manifest_path, package.metadata))
                .build()?
                .try_deserialize()?;

            if flux_metadata.enabled {
                write!(
                    w,
                    r#"
[profile.flux.package."{}"]
rustflags = [{:?}]
                        "#,
                    package.id,
                    flux_metadata
                        .into_flags(&metadata.target_directory)
                        .iter()
                        .chain(flux_flags.iter().flatten())
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
    fn new(origin: impl Into<String>, value: serde_json::Value) -> Self {
        Self { origin: origin.into(), value }
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
            let config_value = serde_json_to_config(&flux_metadata, &self.origin)?;
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
