use std::{env, path::PathBuf, process, str::FromStr, sync::LazyLock};

use clap::Args;
pub use toml::Value;
use tracing::Level;

use crate::{IncludePattern, LeanMode, OverflowMode, PointerWidth, RawDerefMode, SmtSolver};

const FLUX_FLAG_PREFIX: &str = "-F";

macro_rules! flux_arg {
    ($name:literal) => {
        concat!("F", $name)
    };
}

/// Exit status code used for invalid flags.
pub const EXIT_FAILURE: i32 = 2;

#[derive(Args)]
#[command(next_help_heading = "Flux-Specific Flags (Not Yet Supported)")]
pub struct Flags {
    /// Sets the directory to dump data. Defaults to `./log/`.
    #[arg(
        long = flux_arg!("log-dir"),
        value_name = "PATH",
        default_value = "./log/",
    )]
    pub log_dir: PathBuf,
    /// Sets the directory to put all the emitted lean definitions and verification conditions. Defaults to `./`.
    #[arg(
        long = flux_arg!("lean-dir"),
        value_name = "PATH",
        default_value = "./"
    )]
    pub lean_dir: PathBuf,
    /// Name of the lean project. Defaults to `lean_proofs`.
    #[arg(
        long = flux_arg!("lean-project"),
        value_name = "NAME",
        default_value = "lean_proofs"
    )]
    pub lean_project: String,
    /// If present, only check files matching the [`IncludePattern`] a glob pattern.
    #[arg(long = flux_arg!("include"), value_name = "PATTERN", value_parser = panicking_parser)]
    pub include: Option<IncludePattern>,
    /// If present, trust items matching [`IncludePattern`]. This implies `-Finclude`
    #[arg(long = flux_arg!("include-trusted"), value_name = "PATTERN", value_parser = panicking_parser)]
    pub include_trusted: Option<IncludePattern>,
    /// If present, trust items matching [`IncludePattern`]. This implies `-Finclude`
    #[arg(
        long = flux_arg!("include-trusted-impl"),
        value_name = "PATTERN",
        value_parser = panicking_parser
    )]
    pub include_trusted_impl: Option<IncludePattern>,
    /// Set the pointer size (either `32` or `64`), used to determine if an integer cast is lossy
    /// (default `64`).
    #[arg(
        long = flux_arg!("pointer-width"),
        value_name = "WIDTH",
        default_value = "64",
        value_parser = default_pointerwidth
    )]
    pub pointer_width: PointerWidth,
    /// If present switches on query caching and saves the cache in the provided path
    #[arg(long = flux_arg!("cache"), value_name = "PATH", value_parser = panicking_parser)]
    pub cache: Option<PathBuf>,
    /// Compute statistics about number and size of annotations. Dumps file to [`Self::log_dir`]
    #[arg(
        long = flux_arg!("annots"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub annots: bool,
    /// Print statistics about time taken to analyze each fuction. Also dumps a file with the raw
    /// times for each function.
    #[arg(
        long = flux_arg!("timings"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub timings: bool,
    /// Print statistics about number of functions checked, trusted, etc.
    #[arg(
        long = flux_arg!("summary"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub summary: bool,
    /// Default solver. Either `z3` or `cvc5`.
    #[arg(
        long = flux_arg!("solver"),
        value_name = "SOLVER",
        default_value = "z3",
        value_parser = default_smtsolver
    )]
    pub solver: SmtSolver,
    /// Enables qualifier scrapping in fixpoint
    #[arg(
        long = flux_arg!("scrape-quals"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub scrape_quals: bool,
    /// Enables uninterpreted casts
    #[arg(
        long = flux_arg!("allow-uninterpreted-cast"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub allow_uninterpreted_cast: bool,
    /// Translates _monomorphic_ `defs` functions into SMT `define-fun` instead of inlining them
    /// away inside `flux`.
    #[arg(
        long = flux_arg!("smt-define-fun"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub smt_define_fun: bool,
    /// If `strict` checks for over and underflow on arithmetic integer operations,
    /// If `lazy` checks for underflow and loses information if possible overflow,
    /// If `none` (default), it still checks for underflow on unsigned integer subtraction.
    #[arg(
        long = flux_arg!("check-overflow"),
        value_name = "MODE",
        default_value = "none",
        value_parser = default_overflowmode
    )]
    pub check_overflow: OverflowMode,
    /// Whether to allow raw pointer dereferences during refinement checking.
    #[arg(
        long = flux_arg!("allow-raw-deref"),
        value_name = "MODE",
        default_value = "default",
        value_parser = default_rawderefmode
    )]
    pub allow_raw_deref: RawDerefMode,
    /// Dump constraints generated for each function (debugging)
    #[arg(
        long = flux_arg!("dump-constraint"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub dump_constraint: bool,
    /// Saves the checker's trace (debugging)
    #[arg(long = flux_arg!("dump-checker-trace"), value_name = "LEVEL", value_parser = panicking_parser)]
    pub dump_checker_trace: Option<tracing::Level>,
    /// Saves the `fhir` for each item (debugging)
    #[arg(
        long = flux_arg!("dump-fhir"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub dump_fhir: bool,
    /// Saves the the `fhir` (debugging)
    #[arg(
        long = flux_arg!("dump-rty"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub dump_rty: bool,
    /// Optimistically keeps running flux even after errors are found to get as many errors as possible
    #[arg(
        long = flux_arg!("catch-bugs"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub catch_bugs: bool,
    /// Whether verification for the current crate is enabled. If false (the default), `flux-driver`
    /// will behave exactly like `rustc`. This flag is managed by the `cargo flux` and `flux` binaries,
    /// so you don't need to mess with it.
    #[arg(
        long = flux_arg!("verify"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub verify: bool,
    /// If `true`, produce artifacts after analysis. This flag is managed by `cargo flux`, so you
    /// don't typically have to set it manually.
    #[arg(
        long = flux_arg!("full-compilation"),
        num_args = 0..=1,
        default_missing_value = "true"
    )]
    pub full_compilation: bool,
    /// Path to the Flux sysroot directory. If not set, the driver infers it from its own binary location.
    #[arg(long = flux_arg!("sysroot"), value_name = "PATH", value_parser = panicking_parser)]
    pub sysroot: Option<PathBuf>,
    /// If `true`, all code is trusted by default. You can selectively untrust items by marking them with `#[trusted(no)]`. The default value of this flag is `false`, i.e., all code is untrusted by default.
    #[arg(
        long = flux_arg!("trusted"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub trusted_default: bool,
    /// If `true`, all code will be ignored by default. You can selectively unignore items by marking them with `#[ignore(no)]`. The default value of this flag is `false`, i.e., all code is unignored by default.
    #[arg(
        long = flux_arg!("ignore"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub ignore_default: bool,
    #[arg(
        long = flux_arg!("lean"),
        value_name = "MODE",
        default_value = "default",
        value_parser = default_leanmode
    )]
    pub lean: LeanMode,
    /// If `true`, every function is implicitly labeled with a `no_panic` by default.
    #[arg(
        long = flux_arg!("no-panic"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub no_panic: bool,
    /// If `true`, automatically inject `flux_core` and `flux_alloc` as force externs using paths
    /// from `sysroot.toml`. Off by default.
    #[arg(
        long = flux_arg!("std-extern-specs"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub std_extern_specs: bool,
    /// If `true`, produce more detailed error messages (e.g. condition spans for fold errors).
    #[arg(
        long = flux_arg!("flux-verbose"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub flux_verbose: bool,
    /// If `true`, all code will have suggestions disabled.
    #[arg(
        long = flux_arg!("no-suggestions"),
        num_args = 0..=1,
        default_missing_value = "false"
    )]
    pub no_suggestions_default: bool,
}

impl Default for Flags {
    fn default() -> Self {
        Self {
            log_dir: PathBuf::from("./log/"),
            lean_dir: PathBuf::from("./"),
            lean_project: "lean_proofs".to_string(),
            dump_constraint: false,
            dump_checker_trace: None,
            dump_fhir: false,
            dump_rty: false,
            catch_bugs: false,
            pointer_width: PointerWidth::default(),
            include: None,
            include_trusted: None,
            include_trusted_impl: None,
            cache: None,
            check_overflow: OverflowMode::default(),
            allow_raw_deref: RawDerefMode::default(),
            scrape_quals: false,
            allow_uninterpreted_cast: false,
            solver: SmtSolver::default(),
            smt_define_fun: false,
            annots: false,
            timings: false,
            summary: true,
            verify: false,
            full_compilation: false,
            sysroot: None,
            trusted_default: false,
            ignore_default: false,
            lean: LeanMode::default(),
            no_panic: false,
            std_extern_specs: false,
            flux_verbose: false,
            no_suggestions_default: false,
        }
    }
}

pub(crate) static FLAGS: LazyLock<Flags> = LazyLock::new(|| {
    let mut flags = Flags::default();
    let mut includes: Vec<String> = Vec::new();
    let mut trusteds: Vec<String> = Vec::new();
    let mut trusted_impls: Vec<String> = Vec::new();
    for arg in env::args() {
        let Some((key, value)) = parse_flux_arg(&arg) else { continue };

        let result = match key {
            "log-dir" => parse_path_buf(&mut flags.log_dir, value),
            "lean-dir" => parse_path_buf(&mut flags.lean_dir, value),
            "lean-project" => parse_string(&mut flags.lean_project, value),
            "dump-constraint" => parse_bool(&mut flags.dump_constraint, value),
            "dump-checker-trace" => parse_opt_level(&mut flags.dump_checker_trace, value),
            "dump-fhir" => parse_bool(&mut flags.dump_fhir, value),
            "dump-rty" => parse_bool(&mut flags.dump_rty, value),
            "catch-bugs" => parse_bool(&mut flags.catch_bugs, value),
            "pointer-width" => parse_pointer_width(&mut flags.pointer_width, value),
            "check-overflow" => parse_overflow(&mut flags.check_overflow, value),
            "allow-raw-deref" => parse_raw_deref(&mut flags.allow_raw_deref, value),
            "scrape-quals" => parse_bool(&mut flags.scrape_quals, value),
            "allow-uninterpreted-cast" => parse_bool(&mut flags.allow_uninterpreted_cast, value),
            "solver" => parse_solver(&mut flags.solver, value),
            "smt-define-fun" => parse_bool(&mut flags.smt_define_fun, value),
            "annots" => parse_bool(&mut flags.annots, value),
            "timings" => parse_bool(&mut flags.timings, value),
            "summary" => parse_bool(&mut flags.summary, value),
            "cache" => parse_opt_path_buf(&mut flags.cache, value),
            "include" => parse_opt_include(&mut includes, value),
            "include-trusted" => parse_opt_include(&mut trusteds, value),
            "include-trusted-impl" => parse_opt_include(&mut trusted_impls, value),
            "verify" => parse_bool(&mut flags.verify, value),
            "full-compilation" => parse_bool(&mut flags.full_compilation, value),
            "sysroot" => parse_opt_path_buf(&mut flags.sysroot, value),
            "trusted" => parse_bool(&mut flags.trusted_default, value),
            "ignore" => parse_bool(&mut flags.ignore_default, value),
            "lean" => parse_lean_mode(&mut flags.lean, value),
            "no-panic" => parse_bool(&mut flags.no_panic, value),
            "std-extern-specs" => parse_bool(&mut flags.std_extern_specs, value),
            "flux-verbose" => parse_bool(&mut flags.flux_verbose, value),
            "no-suggestions" => parse_bool(&mut flags.no_suggestions_default, value),
            _ => {
                eprintln!("error: unknown flux option: `{key}`");
                process::exit(EXIT_FAILURE);
            }
        };
        if let Err(reason) = result {
            eprintln!("error: incorrect value for flux option `{key}` - `{reason}`");
            process::exit(1);
        }
    }
    if !includes.is_empty() {
        let include = IncludePattern::new(includes).unwrap_or_else(|err| {
            eprintln!("error: invalid include pattern: {err}");
            process::exit(1);
        });
        flags.include = Some(include);
    }
    if !trusteds.is_empty() {
        let trusted = IncludePattern::new(trusteds).unwrap_or_else(|err| {
            eprintln!("error: invalid trusted pattern: {err}");
            process::exit(1);
        });
        flags.include_trusted = Some(trusted);
    }
    if !trusted_impls.is_empty() {
        let trusted_impl = IncludePattern::new(trusted_impls).unwrap_or_else(|err| {
            eprintln!("error: invalid trusted-impl pattern: {err}");
            process::exit(1);
        });
        flags.include_trusted_impl = Some(trusted_impl);
    }
    flags
});

pub fn is_flux_arg(arg: &str) -> bool {
    parse_flux_arg(arg).is_some()
}

fn parse_flux_arg(arg: &str) -> Option<(&str, Option<&str>)> {
    let arg = arg.strip_prefix(FLUX_FLAG_PREFIX)?;
    if arg.is_empty() {
        return None;
    }
    if let Some((k, v)) = arg.split_once('=') { Some((k, Some(v))) } else { Some((arg, None)) }
}

fn parse_bool(slot: &mut bool, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some("y") | Some("yes") | Some("on") | Some("true") | None => {
            *slot = true;
            Ok(())
        }
        Some("n") | Some("no") | Some("off") | Some("false") => {
            *slot = false;
            Ok(())
        }
        _ => {
            Err(
                "expected no value or one of `y`, `yes`, `on`, `true`, `n`, `no`, `off`, or `false`",
            )
        }
    }
}

fn parse_string(slot: &mut String, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.to_string();
            Ok(())
        }
        None => Err("expected a string"),
    }
}

fn parse_path_buf(slot: &mut PathBuf, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = PathBuf::from(s);
            Ok(())
        }
        None => Err("expected a path"),
    }
}

fn parse_pointer_width(slot: &mut PointerWidth, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(PointerWidth::ERROR),
    }
}

fn parse_lean_mode(slot: &mut LeanMode, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(LeanMode::ERROR),
    }
}

fn parse_overflow(slot: &mut OverflowMode, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(OverflowMode::ERROR),
    }
}

fn parse_raw_deref(slot: &mut RawDerefMode, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(RawDerefMode::ERROR),
    }
}

fn parse_solver(slot: &mut SmtSolver, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(SmtSolver::ERROR),
    }
}

fn parse_opt_path_buf(slot: &mut Option<PathBuf>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(PathBuf::from(s));
            Ok(())
        }
        None => Err("expected a path"),
    }
}

fn parse_opt_level(slot: &mut Option<Level>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(Level::from_str(s).map_err(|_| "invalid level")?);
            Ok(())
        }
        None => Err("a level"),
    }
}

fn parse_opt_include(slot: &mut Vec<String>, v: Option<&str>) -> Result<(), &'static str> {
    if let Some(include) = v {
        slot.push(include.to_string());
    }
    Ok(())
}

fn panicking_parser(_s: &str) -> Result<(), String> {
    panic!("Parsing flux args from cli is not yet supported.");
}

fn default_pointerwidth(_s: &str) -> Result<PointerWidth, String> {
    Ok(PointerWidth::default())
}

fn default_overflowmode(_s: &str) -> Result<OverflowMode, String> {
    Ok(OverflowMode::default())
}

fn default_rawderefmode(_s: &str) -> Result<RawDerefMode, String> {
    Ok(RawDerefMode::default())
}

fn default_smtsolver(_s: &str) -> Result<SmtSolver, String> {
    Ok(SmtSolver::default())
}

fn default_leanmode(_s: &str) -> Result<LeanMode, String> {
    Ok(LeanMode::default())
}
