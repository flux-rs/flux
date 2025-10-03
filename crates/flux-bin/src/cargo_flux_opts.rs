use std::path::Path;

use cargo_metadata::{MetadataCommand, camino::Utf8PathBuf};

use crate::{cargo_style, utils::get_version};

#[derive(clap::Parser)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
#[command(styles = cargo_style::CLAP_STYLING)]
pub enum Cli {
    /// Flux's integration with Cargo
    Flux {
        #[command(flatten)]
        check_opts: CheckOpts,

        #[command(subcommand)]
        command: Option<CargoFluxCommand>,
    },
}

#[derive(clap::Subcommand)]
#[command(version = get_version())]
pub enum CargoFluxCommand {
    /// Check a local package and its dependencies for errors using Flux.
    /// This is the default command when no subcommand is provided.
    Check(CheckOpts),
    /// Remove artifacts that cargo-flux has generated in the past
    Clean(CleanOpts),
}

impl CargoFluxCommand {
    /// Returns a vector of arguments to forward to the cargo command
    pub fn forward_args(&self) -> Vec<&str> {
        let mut args = vec![];
        match self {
            CargoFluxCommand::Check(check_opts) => {
                args.push("check");
                check_opts.forward_args(&mut args);
            }
            CargoFluxCommand::Clean(clean_opts) => {
                args.push("clean");
                clean_opts.forward_args(&mut args);
            }
        }
        args
    }

    /// Returns the cargo subcommand
    pub fn cargo_subcommand(&self) -> &'static str {
        match self {
            CargoFluxCommand::Clean(_) => "clean",
            CargoFluxCommand::Check(_) => "check",
        }
    }

    pub fn metadata(&self) -> MetadataCommand {
        let mut meta = cargo_metadata::MetadataCommand::new();
        match self {
            CargoFluxCommand::Check(check_options) => {
                check_options.forward_to_metadata(&mut meta);
            }
            CargoFluxCommand::Clean(clean_options) => {
                clean_options.forward_to_metadata(&mut meta);
            }
        }
        meta
    }
}

#[derive(clap::Args)]
pub struct CheckOpts {
    /// Error format [possible values: human, short, json, json-diagnostic-short, json-diagnostic-rendered-ansi, json-render-diagnostics]
    #[arg(long, value_name = "FMT")]
    message_format: Option<String>,

    #[command(flatten)]
    workspace: Workspace,
    #[command(flatten)]
    features: Features,
    #[command(flatten)]
    manifest: ManifestOptions,
}

impl CheckOpts {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let CheckOpts { message_format, workspace, features, manifest } = self;
        if let Some(message_format) = &message_format {
            args.extend(["--message-format", &message_format]);
        }
        workspace.forward_args(args);
        features.forward_args(args);
        manifest.forward_args(args);
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        let CheckOpts { message_format: _, workspace: _, features, manifest } = self;
        features.forward_to_metadata(meta);
        manifest.forward_to_metadata(meta);
    }
}

#[derive(clap::Args)]
pub struct CleanOpts {
    #[command(flatten, next_help_heading = "Package Selection")]
    package: Package,
    #[command(flatten)]
    features: Features,
    #[command(flatten)]
    manifest: ManifestOptions,
}

impl CleanOpts {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let CleanOpts { package, features, manifest } = self;
        package.forward_args(args);
        features.forward_args(args);
        manifest.forward_args(args);
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        let CleanOpts { package: _, features, manifest } = self;
        features.forward_to_metadata(meta);
        manifest.forward_to_metadata(meta);
    }
}

#[derive(Debug, clap::Args)]
#[command(about = None, long_about = None, next_help_heading = "Package Selection")]
pub struct Workspace {
    #[command(flatten)]
    pub package: Package,

    #[arg(long)]
    /// Process all packages in the workspace
    pub workspace: bool,

    #[arg(long, value_name = "SPEC")]
    /// Exclude packages from being processed
    pub exclude: Vec<String>,
}

impl Workspace {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let Workspace { package, workspace, exclude } = self;
        package.forward_args(args);
        if *workspace {
            args.push("--workspace");
        }
        if !exclude.is_empty() {
            args.extend(exclude.iter().flat_map(|package| ["--exclude", package]));
        }
    }
}

#[derive(Debug, clap::Args)]
#[command(about = None, long_about = None)]
pub struct Package {
    #[arg(short, long, value_name = "SPEC")]
    /// Package to process (see `cargo help pkgid`)
    pub package: Vec<String>,
}

impl Package {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let Package { package } = self;
        if !package.is_empty() {
            args.extend(package.iter().flat_map(|package| ["--package", package]));
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq, clap::Args)]
#[command(about = None, long_about = None, next_help_heading = "Feature Selection")]
pub struct Features {
    #[arg(short = 'F', long, value_delimiter = ' ')]
    /// Space-separated list of features to activate
    pub features: Vec<String>,
    #[arg(long)]
    /// Activate all available features
    pub all_features: bool,
    #[arg(long)]
    /// Do not activate the `default` feature
    pub no_default_features: bool,
}

impl Features {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let Features { features, all_features, no_default_features } = self;
        if !features.is_empty() {
            args.extend(features.iter().flat_map(|feature| ["--features", feature]));
        }
        if *all_features {
            args.push("--all-features");
        }
        if *no_default_features {
            args.push("--no-default-features");
        }
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        let Features { features, all_features, no_default_features } = self;
        if *all_features {
            meta.features(cargo_metadata::CargoOpt::AllFeatures);
        }
        if *no_default_features {
            meta.features(cargo_metadata::CargoOpt::NoDefaultFeatures);
        }
        if !features.is_empty() {
            meta.features(cargo_metadata::CargoOpt::SomeFeatures(features.to_vec()));
        }
    }
}

#[derive(Debug, clap::Args)]
#[command(next_help_heading = "Manifest Options")]
pub struct ManifestOptions {
    #[arg(long, name = "PATH")]
    /// Path to Cargo.toml
    manifest_path: Option<Utf8PathBuf>,
    /// Run without accessing the network
    #[arg(long)]
    offline: bool,
}

impl ManifestOptions {
    fn forward_args<'a>(&'a self, args: &mut Vec<&'a str>) {
        let ManifestOptions { manifest_path, offline } = self;
        if let Some(manifest_path) = &manifest_path {
            args.extend(["--manifest-path", manifest_path.as_str()]);
        }
        if *offline {
            args.push("--offline");
        }
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        // TODO(nilehmann) should we pass offline to metadata?
        let ManifestOptions { manifest_path, offline: _ } = self;
        if let Some(manifest_path) = &manifest_path {
            meta.manifest_path(manifest_path);
        }
    }
}
