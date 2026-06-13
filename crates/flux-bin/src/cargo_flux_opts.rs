use std::{collections::HashSet, path::Path, process::Command};

use cargo_metadata::{
    Metadata, MetadataCommand, Package as CargoPackage, PackageId, camino::Utf8PathBuf,
};
use flux_config::flags::Flags;

use crate::cargo_style;

#[derive(clap::Parser)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
#[command(styles = cargo_style::CLAP_STYLING)]
pub enum Cli {
    /// Flux's integration with Cargo
    Flux {
        #[command(flatten)]
        check_opts: CompileOpts,

        #[command(subcommand)]
        command: Option<CargoFluxCommand>,

        /// Print version information
        #[arg(short = 'V', long, action = clap::ArgAction::SetTrue)]
        version: bool,

        /// Use verbose output (-Vv for more verbose output)
        #[arg(short, long, action = clap::ArgAction::Count)]
        verbose: u8,
    },
}

#[derive(clap::Subcommand)]
pub enum CargoFluxCommand {
    /// Check a local package and its dependencies for errors using Flux.
    /// This is the default command when no subcommand is provided.
    Check(CompileOpts),
    /// Compile a local package and its dependencies using Flux.
    Build(CompileOpts),
    /// Remove artifacts that cargo-flux has generated in the past
    Clean(CleanOpts),
}

impl CargoFluxCommand {
    pub fn forward_args(&self, cmd: &mut Command, config_file: &Path) {
        match self {
            CargoFluxCommand::Check(check_opts) => {
                if check_opts.fix {
                    // `cargo fix` applies span_suggestion replacements written by flux-driver.
                    //
                    // Mechanism: cargo fix sets RUSTC_WORKSPACE_WRAPPER to a self-re-exec proxy
                    // that runs flux-driver (our RUSTC) with --error-format=json, parses the
                    // resulting diagnostic JSON for suggested_replacement spans, and applies them
                    // via rustfix. This is the same pipeline Clippy uses, just with RUSTC= instead
                    // of RUSTC_WORKSPACE_WRAPPER= on our side; the two env vars are independent.
                    cmd.arg("fix")
                        // Implies broken-code (since Flux errors are not
                        // warnings, it wouldn't apply otherwise).
                        .arg("--broken-code");
                } else {
                    cmd.arg("check");
                }
                check_opts.forward_args(cmd);
            }
            CargoFluxCommand::Build(build_opts) => {
                cmd.arg("build");
                build_opts.forward_args(cmd);
            }
            CargoFluxCommand::Clean(clean_opts) => {
                cmd.arg("clean");
                clean_opts.forward_args(cmd);
            }
        }
        cmd.args(["--profile", "flux"]);
        cmd.args(["--config".as_ref(), config_file.as_os_str()]);
    }

    pub fn metadata(&self) -> MetadataCommand {
        let mut meta = cargo_metadata::MetadataCommand::new();
        match self {
            CargoFluxCommand::Check(check_options) | CargoFluxCommand::Build(check_options) => {
                check_options.forward_to_metadata(&mut meta);
            }
            CargoFluxCommand::Clean(clean_options) => {
                clean_options.forward_to_metadata(&mut meta);
            }
        }
        meta
    }

    pub fn targeted_package_ids(&self, metadata: &Metadata) -> HashSet<PackageId> {
        match self {
            CargoFluxCommand::Check(opts) | CargoFluxCommand::Build(opts) => {
                opts.targeted_package_ids(metadata)
            }
            CargoFluxCommand::Clean(opts) => opts.targeted_package_ids(metadata),
        }
    }

    pub fn only_check(&self) -> Option<&str> {
        match self {
            CargoFluxCommand::Check(opts) | CargoFluxCommand::Build(opts) => {
                opts.only_check.as_deref()
            }
            CargoFluxCommand::Clean(_) => None,
        }
    }
}

#[derive(clap::Args)]
pub struct CompileOpts {
    /// Error format [possible values: human, short, json, json-diagnostic-short, json-diagnostic-rendered-ansi, json-render-diagnostics]
    #[arg(long, value_name = "FMT")]
    message_format: Option<String>,

    #[command(flatten)]
    workspace: Workspace,
    #[command(flatten)]
    features: Features,
    #[command(flatten)]
    compilation: CompilationOptions,
    #[command(flatten)]
    manifest: ManifestOptions,
    #[command(flatten)]
    flux_flags: Flags,

    /// Only check items matching PATTERN (overrides include patterns from cargo.toml or flux.toml).
    ///
    /// Supported patterns:
    ///   def:<name>              — match items whose name contains <name>
    ///   span:<file>:<line>:<col> — match the item at a source location
    ///   glob:<pattern>          — match files by glob (e.g. "glob:src/ascii/*.rs")
    ///   <pattern>               — bare string treated as a glob
    #[arg(long, value_name = "PATTERN")]
    pub only_check: Option<String>,

    /// Automatically apply Flux's suggested annotations to the source code
    /// using 'cargo fix'.
    ///
    /// Implies --broken-code.
    #[arg(long)]
    pub fix: bool,

    #[command(flatten)]
    fix_opts: FixOpts,
}

impl CompileOpts {
    fn forward_args(&self, cmd: &mut Command) {
        let CompileOpts {
            message_format,
            workspace,
            features,
            compilation,
            manifest,
            fix: _,
            fix_opts,
            ..
        } = self;
        if let Some(message_format) = &message_format {
            cmd.args(["--message-format", message_format]);
        }
        workspace.forward_args(cmd);
        features.forward_args(cmd);
        compilation.forward_args(cmd);
        manifest.forward_args(cmd);
        fix_opts.forward_args(cmd);
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        let CompileOpts { features, manifest, fix: _, fix_opts: _, .. } = self;
        features.forward_to_metadata(meta);
        manifest.forward_to_metadata(meta);
    }

    pub fn targeted_package_ids(&self, metadata: &Metadata) -> HashSet<PackageId> {
        targeted_package_ids(&self.workspace, metadata)
    }
}

fn package_matches_spec(package: &CargoPackage, spec: &str) -> bool {
    if package.id.repr == spec {
        return true;
    }

    if let Some((name, version)) = spec.rsplit_once('@') {
        return package.name == name && package.version.to_string() == version;
    }

    package.name == spec
}

fn select_packages_by_spec<'a>(package: &Package, metadata: &'a Metadata) -> Vec<&'a CargoPackage> {
    let workspace_packages = metadata.workspace_packages();
    if !package.package.is_empty() {
        workspace_packages
            .into_iter()
            .filter(|p| {
                package
                    .package
                    .iter()
                    .any(|spec| package_matches_spec(p, spec))
            })
            .collect()
    } else if metadata.workspace_default_members.is_available() {
        metadata.workspace_default_packages()
    } else if let Some(root) = metadata.root_package() {
        vec![root]
    } else {
        workspace_packages
    }
}

fn targeted_package_ids(workspace: &Workspace, metadata: &Metadata) -> HashSet<PackageId> {
    let mut packages = if workspace.workspace {
        metadata.workspace_packages()
    } else {
        select_packages_by_spec(&workspace.package, metadata)
    };

    packages.retain(|p| {
        !workspace
            .exclude
            .iter()
            .any(|spec| package_matches_spec(p, spec))
    });

    packages.into_iter().map(|p| p.id.clone()).collect()
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
    fn forward_args(&self, cmd: &mut Command) {
        let CleanOpts { package, features, manifest } = self;
        package.forward_args(cmd);
        features.forward_args(cmd);
        manifest.forward_args(cmd);
    }

    fn forward_to_metadata(&self, meta: &mut MetadataCommand) {
        let CleanOpts { package: _, features, manifest } = self;
        features.forward_to_metadata(meta);
        manifest.forward_to_metadata(meta);
    }

    pub fn targeted_package_ids(&self, metadata: &Metadata) -> HashSet<PackageId> {
        select_packages_by_spec(&self.package, metadata)
            .into_iter()
            .map(|p| p.id.clone())
            .collect()
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
    fn forward_args(&self, cmd: &mut Command) {
        let Workspace { package, workspace, exclude } = self;
        package.forward_args(cmd);
        if *workspace {
            cmd.arg("--workspace");
        }
        if !exclude.is_empty() {
            cmd.args(exclude.iter().flat_map(|package| ["--exclude", package]));
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
    fn forward_args(&self, cmd: &mut Command) {
        let Package { package } = self;
        if !package.is_empty() {
            cmd.args(package.iter().flat_map(|package| ["--package", package]));
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
    fn forward_args(&self, cmd: &mut Command) {
        let Features { features, all_features, no_default_features } = self;
        if !features.is_empty() {
            cmd.args(features.iter().flat_map(|feature| ["--features", feature]));
        }
        if *all_features {
            cmd.arg("--all-features");
        }
        if *no_default_features {
            cmd.arg("--no-default-features");
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
            meta.features(cargo_metadata::CargoOpt::SomeFeatures(features.clone()));
        }
    }
}

#[derive(Debug, clap::Args)]
#[command(next_help_heading = "Compilation Options")]
pub struct CompilationOptions {
    #[arg(short = 'j', long, value_name = "N")]
    /// Number of parallel jobs, defaults to # of CPUs.
    pub jobs: Option<u32>,
    #[arg(long)]
    /// Do not abort the build as soon as there is an error
    pub keep_going: bool,
    #[arg(long, value_name = "TRIPLE")]
    /// Check for the target triple
    pub target: Vec<String>,
}

impl CompilationOptions {
    fn forward_args(&self, cmd: &mut Command) {
        let CompilationOptions { jobs, keep_going, target } = self;
        if let Some(jobs) = jobs {
            cmd.args(["--jobs", &format!("{jobs}")]);
        }
        if *keep_going {
            cmd.arg("--keep-going");
        }
        for t in target {
            cmd.args(["--target", t]);
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
    fn forward_args(&self, cmd: &mut Command) {
        let ManifestOptions { manifest_path, offline } = self;
        if let Some(manifest_path) = &manifest_path {
            cmd.args(["--manifest-path", manifest_path.as_str()]);
        }
        if *offline {
            cmd.arg("--offline");
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

/// Options forwarded verbatim to `cargo fix` when `--fix` is passed.
/// These are ignored when running `cargo check`.
#[derive(Default, Debug, clap::Args)]
#[command(about = None, long_about = None, next_help_heading = "Fix Options")]
pub struct FixOpts {
    /// Don't require a clean git working directory when running `--fix`.
    #[arg(long, requires = "fix")]
    allow_dirty: bool,

    /// Don't require a staged git index when running `--fix`.
    #[arg(long, requires = "fix")]
    allow_staged: bool,
}

impl FixOpts {
    fn forward_args(&self, cmd: &mut Command) {
        let FixOpts { allow_dirty, allow_staged } = self;
        if *allow_dirty {
            cmd.arg("--allow-dirty");
        }
        if *allow_staged {
            cmd.arg("--allow-staged");
        }
    }
}
