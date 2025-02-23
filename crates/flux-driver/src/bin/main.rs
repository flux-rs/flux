#![feature(rustc_private)]

extern crate rustc_driver;

use std::{
    env, fs,
    io::{self, Read as _},
    ops::Deref,
    path::{Path, PathBuf},
    process::exit,
};

use flux_driver::callbacks::FluxCallbacks;
use rustc_driver::{catch_with_exit_code, run_compiler};

mod logger;

fn main() -> io::Result<()> {
    let original_args = env::args().collect::<Vec<_>>();

    let resolve_logs = logger::install()?;

    let context = Context::new(&original_args);

    if context.be_rustc() {
        rustc_driver::install_ice_hook(rustc_driver::DEFAULT_BUG_REPORT_URL, |_| ());
        rustc_driver::main();
    }

    // HACK(nilehmann)
    // Disable incremental compilation because that makes the borrow checker to not run
    // and we fail to retrieve the mir.
    let mut args = vec![];
    let mut is_codegen = false;
    for arg in env::args() {
        if arg.starts_with("-C") || arg.starts_with("--codegen") {
            is_codegen = true;
        } else if is_codegen && arg.starts_with("incremental=") {
            is_codegen = false;
        } else {
            if is_codegen {
                args.push("-C".to_string());
                is_codegen = false;
            }
            args.push(arg);
        }
    }

    args.push("--sysroot".into());
    args.push(sysroot().expect("Flux Rust requires rustup to be built."));
    args.push("-Coverflow-checks=off".to_string());
    args.push("-Zcrate-attr=feature(register_tool, custom_inner_attributes)".to_string());
    args.push("-Zcrate-attr=register_tool(flux)".to_string());
    args.push("-Zcrate-attr=register_tool(flux_tool)".to_string());
    args.push("--cfg=flux".to_string());

    let mut callbacks =
        FluxCallbacks { full_compilation: context.full_compilation(), verify: context.verify() };

    let exit_code = catch_with_exit_code(move || {
        run_compiler(&args, &mut callbacks);
        Ok(())
    });
    resolve_logs()?;
    exit(exit_code)
}

/// Get the path to the sysroot of the current rustup toolchain. Return `None` if the rustup
/// environment variables are not set.
fn sysroot() -> Option<String> {
    let home = option_env!("RUSTUP_HOME")?;
    let toolchain = option_env!("RUSTUP_TOOLCHAIN")?;
    Some(format!("{home}/toolchains/{toolchain}"))
}

/// If a command-line option matches `find_arg`, then apply the predicate `pred` on its value. If
/// true, then return it. The parameter is assumed to be either `--arg=value` or `--arg value`.
pub fn arg_value<'a, T: Deref<Target = str>>(
    args: &'a [T],
    find_arg: &str,
    pred: impl Fn(&str) -> bool,
) -> Option<&'a str> {
    let mut args = args.iter().map(Deref::deref);
    while let Some(arg) = args.next() {
        let mut arg = arg.splitn(2, '=');
        if arg.next() != Some(find_arg) {
            continue;
        }

        match arg.next().or_else(|| args.next()) {
            Some(v) if pred(v) => return Some(v),
            _ => {}
        }
    }
    None
}

struct FluxMetadata {
    enabled: bool,
}

impl FluxMetadata {
    fn read() -> Option<FluxMetadata> {
        let Ok(manifest_dir) = env::var("CARGO_MANIFEST_DIR") else {
            return None;
        };
        let manifest_dir = PathBuf::from(manifest_dir);
        let manifest = FluxMetadata::read_manifest(&manifest_dir);
        let enabled = manifest
            .get("package")
            .and_then(|package| package.get("metadata"))
            .and_then(|metadata| metadata.get("flux"))
            .and_then(|flux| flux.get("enabled"))
            .and_then(toml::Value::as_bool)
            .unwrap_or(false);
        Some(FluxMetadata { enabled })
    }

    fn read_manifest(manifest_dir: &Path) -> toml::Value {
        let manifest_path = manifest_dir.join("Cargo.toml");
        let mut contents = String::new();
        let mut file = fs::File::open(manifest_path).unwrap();
        file.read_to_string(&mut contents).unwrap();
        toml::from_str(&contents).unwrap()
    }
}

/// The context in which `flux-driver` is being called.
enum Context {
    /// Called from `cargo-flux`
    CargoFlux {
        /// Whether the driver was invoked with `--crate-name build_script_build`. Passed from
        /// cargo when executing `build.rs`.
        build_script_build: bool,
        /// Metadata in the `Cargo.toml` manifest
        metadata: Option<FluxMetadata>,
    },
    /// Called from `flux` binary
    Flux {
        /// Whether full compilation if forced via `FLUX_FULL_COMPILATION`
        force_full_compilation: bool,
    },
}

impl Context {
    fn new(args: &[String]) -> Context {
        if env::var("FLUX_CARGO").is_ok() {
            let build_script_build =
                arg_value(args, "--crate-name", |val| val == "build_script_build").is_some();
            Context::CargoFlux { build_script_build, metadata: FluxMetadata::read() }
        } else {
            let force_full_compilation = env_var_is("FLUX_FULL_COMPILATION", "1");
            Context::Flux { force_full_compilation }
        }
    }

    fn be_rustc(&self) -> bool {
        match self {
            Context::CargoFlux { build_script_build, metadata: manifest } => {
                *build_script_build || manifest.is_none()
            }
            Context::Flux { .. } => false,
        }
    }

    /// Whether the target crate should be verified. We verify a crate if we are being called from
    /// `flux` on a single file or if Flux is explicitly enabled in the manifest.
    fn verify(&self) -> bool {
        match self {
            Context::CargoFlux { metadata: Some(FluxMetadata { enabled }), .. } => *enabled,
            Context::CargoFlux { metadata: None, .. } => false,
            Context::Flux { .. } => true,
        }
    }

    /// Whether to do a full compilation, i.e., continue after verification to generate artifacts.
    /// We always do a full compilation when called from `cargo-flux`. When called from `flux`
    /// we stop after verification so we don't generate artifacts unless full compilation is forced
    /// via an environment variable.
    fn full_compilation(&self) -> bool {
        matches!(self, Context::CargoFlux { .. } | Context::Flux { force_full_compilation: true })
    }
}

fn env_var_is(name: &str, test: &str) -> bool {
    let Ok(val) = env::var(name) else { return false };
    val == test
}
