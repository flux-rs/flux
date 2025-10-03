use std::path::PathBuf;

use cargo_metadata::MetadataCommand;

use crate::{cargo_style, utils::get_version};

#[derive(clap::Parser)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
#[command(styles = cargo_style::CLAP_STYLING)]
pub enum Cli {
    /// Flux's integration with Cargo
    Flux {
        #[command(flatten)]
        check_opts: CheckOptions,

        #[command(flatten)]
        global_opts: GlobalOptions,

        #[command(subcommand)]
        command: Option<CargoFluxCommand>,
    },
}

#[derive(Debug, clap::Args)]
#[command(about = None, long_about = None, next_help_heading = "Package Selection")]
pub struct Workspace {
    #[arg(short, long, value_name = "SPEC", global = true)]
    /// Package to process (see `cargo help pkgid`)
    pub package: Vec<String>,
    #[arg(long, global = true)]
    /// Process all packages in the workspace
    pub workspace: bool,
    #[arg(long, value_name = "SPEC", global = true)]
    /// Exclude packages from being processed
    pub exclude: Vec<String>,
}

#[derive(Default, Clone, Debug, PartialEq, Eq, clap::Args)]
#[command(about = None, long_about = None, next_help_heading = "Feature Selection")]
pub struct Features {
    #[arg(short = 'F', long, value_delimiter = ' ', global = true)]
    /// Space-separated list of features to activate
    pub features: Vec<String>,
    #[arg(long, global = true)]
    /// Activate all available features
    pub all_features: bool,
    #[arg(long, global = true)]
    /// Do not activate the `default` feature
    pub no_default_features: bool,
}

#[derive(Debug, clap::Args)]
#[command(version = get_version())]
pub struct GlobalOptions {
    #[command(flatten)]
    workspace: Workspace,
    #[command(flatten)]
    features: Features,
    #[command(flatten)]
    manifest: ManifestOptions,
}

#[derive(Debug, clap::Args)]
#[command(next_help_heading = "Manifest Options")]
pub struct ManifestOptions {
    #[arg(long, name = "PATH", global = true)]
    /// Path to Cargo.toml
    manifest_path: Option<PathBuf>,
    /// Run without accessing the network
    #[arg(long, global = true)]
    offline: bool,
}

#[derive(clap::Args)]
pub struct CheckOptions {
    /// Error format [possible values: human, short, json, json-diagnostic-short, json-diagnostic-rendered-ansi, json-render-diagnostics]
    #[arg(long, value_name = "FMT")]
    message_format: Option<String>,
}

#[derive(clap::Subcommand)]
pub enum CargoFluxCommand {
    /// Check a local package and its dependencies for errors using Flux.
    /// This is the default command when no subcommand is provided.
    Check(CheckOptions),
    /// Remove artifacts that cargo-flux has generated in the past
    Clean,
}

impl GlobalOptions {
    /// Returns a vector of arguments to forward to the cargo command
    pub fn forward_args(&self) -> Vec<&str> {
        let mut forward_args = vec![];
        if !self.features.features.is_empty() {
            forward_args.extend(
                self.features
                    .features
                    .iter()
                    .flat_map(|feature| ["--features", feature]),
            );
        }
        if self.features.all_features {
            forward_args.push("--all-features");
        }
        if self.features.no_default_features {
            forward_args.push("--no-default-features");
        }
        if self.manifest.offline {
            forward_args.push("--offline");
        }
        if !self.workspace.package.is_empty() {
            forward_args.extend(
                self.workspace
                    .package
                    .iter()
                    .flat_map(|package| ["--package", package]),
            );
        }
        if self.workspace.workspace {
            forward_args.push("--workspace");
        }
        if !self.workspace.exclude.is_empty() {
            forward_args.extend(
                self.workspace
                    .exclude
                    .iter()
                    .flat_map(|package| ["--exclude", package]),
            );
        }
        forward_args
    }

    pub fn metadata(&self) -> MetadataCommand {
        let mut meta = cargo_metadata::MetadataCommand::new();
        if let Some(ref manifest_path) = self.manifest.manifest_path {
            meta.manifest_path(manifest_path);
        }
        if self.features.all_features {
            meta.features(cargo_metadata::CargoOpt::AllFeatures);
        }
        if self.features.no_default_features {
            meta.features(cargo_metadata::CargoOpt::NoDefaultFeatures);
        }
        if !self.features.features.is_empty() {
            meta.features(cargo_metadata::CargoOpt::SomeFeatures(self.features.features.to_vec()));
        }
        meta
    }
}

impl CargoFluxCommand {
    /// Returns a vector of arguments to forward to the cargo command
    pub fn forward_args(&self) -> Vec<&str> {
        let mut forward_args = vec![];
        match self {
            CargoFluxCommand::Check(check_args) => {
                if let Some(message_format) = &check_args.message_format {
                    forward_args.push("--message-format");
                    forward_args.push(&message_format);
                }
            }
            CargoFluxCommand::Clean => {}
        }
        forward_args
    }

    /// Returns the cargo subcommand
    pub fn cargo_subcommand(&self) -> &'static str {
        match self {
            CargoFluxCommand::Clean => "clean",
            CargoFluxCommand::Check { .. } => "check",
        }
    }
}
