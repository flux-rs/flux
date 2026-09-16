use std::{env, fmt::Display, path::PathBuf, process, str::FromStr, sync::LazyLock};

use clap::Args;
pub use toml::Value;
use tracing::Level;

use crate::{IncludePattern, LeanMode, OverflowMode, PointerWidth, RawDerefMode, SmtSolver};

const FLUX_FLAG_PREFIX: &str = "-F";

/// Defaults for flags.
pub const DUMP_CONSTRAINT: bool = false;
pub const DUMP_FHIR: bool = false;
pub const DUMP_RTY: bool = false;
pub const LOG_DIR: &str = "./log/";
pub const LEAN_DIR: &str = "./";
pub const LEAN_PROJECT: &str = "lean_proofs";
pub const TRUSTED_DEFAULT: bool = false;
pub const IGNORE_DEFAULT: bool = false;
pub const ALLOW_UNINTERPRETED_CAST: bool = false;
pub const SCRAPE_QUALS: bool = false;
pub const NO_PANIC: bool = false;
pub const SMT_DEFINE_FUN: bool = false;
pub const CATCH_BUGS: bool = false;
pub const ANNOTS: bool = false;
pub const TIMINGS: bool = false;
pub const VERIFY: bool = false;
pub const SUMMARY: bool = true;
pub const FULL_COMPILATION: bool = false;
pub const STD_EXTERN_SPECS: bool = false;
pub const VERBOSE: bool = false;
pub const NO_SUGGESTIONS_DEFAULT: bool = false;
pub const RERUN_HINT: bool = true;

macro_rules! flux_arg {
    ($name:literal) => {
        concat!("F", $name)
    };
}

/// Exit status code used for invalid flags.
pub const EXIT_FAILURE: i32 = 2;

/// Flux specific flags. Note that all of these are options, since we don't want to make defaults here override
/// other flags from per-crate config files.
#[derive(Args, Default)]
#[command(next_help_heading = "Flux-Specific Flags")]
pub struct Flags {
    /// Sets the directory to dump data. Defaults to `./log/`.
    #[arg(long = flux_arg!("log-dir"), value_name = "PATH")]
    pub log_dir: Option<PathBuf>,
    /// Sets the directory to put all the emitted lean definitions and verification conditions. Defaults to `./`.
    #[arg(long = flux_arg!("lean-dir"), value_name = "PATH")]
    pub lean_dir: Option<PathBuf>,
    /// Name of the lean project. Defaults to `lean_proofs`.
    #[arg(long = flux_arg!("lean-project"), value_name = "NAME")]
    pub lean_project: Option<String>,
    /// If present, only check files matching the [`IncludePattern`] (a glob pattern).
    #[arg(long = flux_arg!("include"), value_name = "PATTERN", value_parser = parse_include_value)]
    pub include: Option<IncludePattern>,
    /// If present, trust items matching [`IncludePattern`]. This implies `-Finclude`
    #[arg(long = flux_arg!("include-trusted"), value_name = "PATTERN", value_parser = parse_include_value)]
    pub include_trusted: Option<IncludePattern>,
    /// If present, trust items matching [`IncludePattern`]. This implies `-Finclude`
    #[arg(
        long = flux_arg!("include-trusted-impl"),
        value_name = "PATTERN",
        value_parser = parse_include_value
    )]
    pub include_trusted_impl: Option<IncludePattern>,
    /// Set the pointer size (either `32` or `64`), used to determine if an integer cast is lossy
    /// (default `64`).
    #[arg(
        long = flux_arg!("pointer-width"),
        value_name = "WIDTH",
        value_parser = parse_pointer_width_value
    )]
    pub pointer_width: Option<PointerWidth>,
    /// If present, switches on query caching and saves the cache in the provided path
    #[arg(long = flux_arg!("cache"), value_name = "PATH")]
    pub cache: Option<PathBuf>,
    /// Compute statistics about number and size of annotations. Dumps file to [`Self::log_dir`].
    /// Defaults to `false`.
    #[arg(
        long = flux_arg!("annots"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub annots: Option<bool>,
    /// Print statistics about time taken to analyze each function. Also dumps a file with the raw
    /// times for each function. Defaults to `false`.
    #[arg(
        long = flux_arg!("timings"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub timings: Option<bool>,
    /// Print statistics about number of functions checked, trusted, etc. Defaults to `true`.
    #[arg(
        long = flux_arg!("summary"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub summary: Option<bool>,
    /// Default solver. Either `z3` or `cvc5`.
    #[arg(
        long = flux_arg!("solver"),
        value_name = "SOLVER",
        value_parser = parse_solver_value
    )]
    pub solver: Option<SmtSolver>,
    /// Enables qualifier scrapping in fixpoint. Defaults to `false`.
    #[arg(
        long = flux_arg!("scrape-quals"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub scrape_quals: Option<bool>,
    /// Enables uninterpreted casts. Defaults to `false`.
    #[arg(
        long = flux_arg!("allow-uninterpreted-cast"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub allow_uninterpreted_cast: Option<bool>,
    /// Translates _monomorphic_ `defs` functions into SMT `define-fun` instead of inlining them
    /// away inside `flux`. Defaults to `false`.
    #[arg(
        long = flux_arg!("smt-define-fun"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub smt_define_fun: Option<bool>,
    /// If `strict` checks for over and underflow on arithmetic integer operations,
    /// If `lazy` checks for underflow and loses information if possible overflow,
    /// If `none` (default), it still checks for underflow on unsigned integer subtraction.
    #[arg(
        long = flux_arg!("check-overflow"),
        value_name = "MODE",
        value_parser = parse_overflow_value
    )]
    pub check_overflow: Option<OverflowMode>,
    /// Whether to allow raw pointer dereferences during refinement checking.
    #[arg(
        long = flux_arg!("allow-raw-deref"),
        value_name = "MODE",
        value_parser = parse_raw_deref_value
    )]
    pub allow_raw_deref: Option<RawDerefMode>,
    /// Dump constraints generated for each function (debugging). Defaults to `false`.
    #[arg(
        long = flux_arg!("dump-constraint"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub dump_constraint: Option<bool>,
    /// Saves the checker's trace (debugging).
    #[arg(long = flux_arg!("dump-checker-trace"), value_name = "LEVEL", value_parser = parse_level_value)]
    pub dump_checker_trace: Option<tracing::Level>,
    /// Saves the `fhir` for each item (debugging). Defaults to `false`.
    #[arg(
        long = flux_arg!("dump-fhir"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub dump_fhir: Option<bool>,
    /// Saves the the `fhir` (debugging). Defaults to `false`.
    #[arg(
        long = flux_arg!("dump-rty"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub dump_rty: Option<bool>,
    /// Optimistically keeps running flux even after errors are found to get as many errors as possible.
    /// Defaults to `false`.
    #[arg(
        long = flux_arg!("catch-bugs"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub catch_bugs: Option<bool>,
    /// Whether verification for the current crate is enabled. If false (the default), `flux-driver`
    /// will behave exactly like `rustc`. This flag is managed by the `cargo flux` and `flux` binaries,
    /// so you don't need to mess with it.
    #[arg(
        long = flux_arg!("verify"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub verify: Option<bool>,
    /// If `true`, produce artifacts after analysis. This flag is managed by `cargo flux`, so you
    /// don't typically have to set it manually.
    #[arg(
        long = flux_arg!("full-compilation"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub full_compilation: Option<bool>,
    /// Path to the Flux sysroot directory. If not set, the driver infers it from its own binary location.
    #[arg(long = flux_arg!("sysroot"), value_name = "PATH")]
    pub sysroot: Option<PathBuf>,
    /// If `true`, all code is trusted by default. You can selectively untrust items by marking them with `#[trusted(no)]`. The default value of this flag is `false`, i.e., all code is untrusted by default.
    #[arg(
        long = flux_arg!("trusted"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub trusted_default: Option<bool>,
    /// If `true`, all code will be ignored by default. You can selectively unignore items by marking them with `#[ignore(no)]`. The default value of this flag is `false`, i.e., all code is unignored by default.
    #[arg(
        long = flux_arg!("ignore"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub ignore_default: Option<bool>,
    #[arg(long = flux_arg!("lean"), value_name = "MODE", value_parser = parse_lean_value)]
    pub lean: Option<LeanMode>,
    /// If `true`, every function is implicitly labeled with a `no_panic` by default. Defaults to `false`.
    #[arg(
        long = flux_arg!("no-panic"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub no_panic: Option<bool>,
    /// If `true`, automatically inject `flux_core` and `flux_alloc` as force externs using paths
    /// from `sysroot.toml`. Off by default.
    #[arg(
        long = flux_arg!("std-extern-specs"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub std_extern_specs: Option<bool>,
    /// If `true`, produce more detailed error messages (e.g. condition spans for fold errors).
    /// Defaults to `false`.
    #[arg(
        long = flux_arg!("flux-verbose"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub flux_verbose: Option<bool>,
    /// If `true`, all code will have suggestions disabled. Defaults to `false`.
    #[arg(
        long = flux_arg!("no-suggestions"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub no_suggestions_default: Option<bool>,
    /// If `true` (the default), attach a note to each failing item with a copy-pasteable command to
    /// re-run the check on just that item. Only applies when running under `cargo flux`.
    #[arg(
        long = flux_arg!("rerun-hint"),
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = parse_bool_value
    )]
    pub rerun_hint: Option<bool>,
}

fn flag<T: Display>(flags: &mut Vec<String>, name: &str, value: Option<T>) {
    flags.extend(value.map(|v| format!("-F{name}={v}")));
}

fn flag_include_pat(flags: &mut Vec<String>, name: &str, value: Option<&IncludePattern>) {
    if let Some(pat) = value {
        flags.extend(pat.originals.iter().map(|raw| format!("-F{name}={raw}")));
    }
}

impl Flags {
    // Convert this struct into what we'd need to pass in through the environment var
    pub fn rustflags(&self) -> Vec<String> {
        let mut flags = Vec::new();
        flag(&mut flags, "log-dir", self.log_dir.as_ref().map(|v| v.display()));
        flag(&mut flags, "lean-dir", self.lean_dir.as_ref().map(|v| v.display()));
        flag(&mut flags, "lean-project", self.lean_project.as_ref());
        flag_include_pat(&mut flags, "include", self.include.as_ref());
        flag_include_pat(&mut flags, "include-trusted", self.include_trusted.as_ref());
        flag_include_pat(&mut flags, "include-trusted-impl", self.include_trusted_impl.as_ref());
        flag(&mut flags, "pointer-width", self.pointer_width.map(|v| v.bits()));
        flag(&mut flags, "cache", self.cache.as_ref().map(|v| v.display()));
        flag(&mut flags, "annots", self.annots);
        flag(&mut flags, "timings", self.timings);
        flag(&mut flags, "summary", self.summary);
        flag(&mut flags, "solver", self.solver);
        flag(&mut flags, "scrape-quals", self.scrape_quals);
        flag(&mut flags, "allow-uninterpreted-cast", self.allow_uninterpreted_cast);
        flag(&mut flags, "smt-define-fun", self.smt_define_fun);
        flag(&mut flags, "check-overflow", self.check_overflow);
        flag(&mut flags, "allow-raw-deref", self.allow_raw_deref);
        flag(&mut flags, "dump-constraint", self.dump_constraint);
        flag(
            &mut flags,
            "dump-checker-trace",
            self.dump_checker_trace.map(|v| v.as_str().to_lowercase()),
        );
        flag(&mut flags, "dump-fhir", self.dump_fhir);
        flag(&mut flags, "dump-rty", self.dump_rty);
        flag(&mut flags, "catch-bugs", self.catch_bugs);
        flag(&mut flags, "verify", self.verify);
        flag(&mut flags, "full-compilation", self.full_compilation);
        flag(&mut flags, "sysroot", self.sysroot.as_ref().map(|v| v.display()));
        flag(&mut flags, "trusted", self.trusted_default);
        flag(&mut flags, "ignore", self.ignore_default);
        flag(&mut flags, "lean", self.lean);
        flag(&mut flags, "no-panic", self.no_panic);
        flag(&mut flags, "std-extern-specs", self.std_extern_specs);
        flag(&mut flags, "flux-verbose", self.flux_verbose);
        flag(&mut flags, "no-suggestions", self.no_suggestions_default);
        flag(&mut flags, "rerun-hint", self.rerun_hint);
        flags
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
            "log-dir" => parse_path(&mut flags.log_dir, value),
            "lean-dir" => parse_path(&mut flags.lean_dir, value),
            "lean-project" => parse_string(&mut flags.lean_project, value),
            "dump-constraint" => parse_bool(&mut flags.dump_constraint, value),
            "dump-checker-trace" => parse_level(&mut flags.dump_checker_trace, value),
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
            "cache" => parse_path(&mut flags.cache, value),
            "include" => parse_include(&mut includes, value),
            "include-trusted" => parse_include(&mut trusteds, value),
            "include-trusted-impl" => parse_include(&mut trusted_impls, value),
            "verify" => parse_bool(&mut flags.verify, value),
            "full-compilation" => parse_bool(&mut flags.full_compilation, value),
            "sysroot" => parse_path(&mut flags.sysroot, value),
            "trusted" => parse_bool(&mut flags.trusted_default, value),
            "ignore" => parse_bool(&mut flags.ignore_default, value),
            "lean" => parse_lean_mode(&mut flags.lean, value),
            "no-panic" => parse_bool(&mut flags.no_panic, value),
            "std-extern-specs" => parse_bool(&mut flags.std_extern_specs, value),
            "flux-verbose" => parse_bool(&mut flags.flux_verbose, value),
            "no-suggestions" => parse_bool(&mut flags.no_suggestions_default, value),
            "rerun-hint" => parse_bool(&mut flags.rerun_hint, value),
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

fn decode_bool(v: Option<&str>) -> Result<bool, &'static str> {
    match v {
        Some("y") | Some("yes") | Some("on") | Some("true") | None => Ok(true),
        Some("n") | Some("no") | Some("off") | Some("false") => Ok(false),
        _ => {
            Err(
                "expected no value or one of `y`, `yes`, `on`, `true`, `n`, `no`, `off`, or `false`",
            )
        }
    }
}

fn parse_bool(slot: &mut Option<bool>, v: Option<&str>) -> Result<(), &'static str> {
    decode_bool(v).map(|b| *slot = Some(b))
}

fn parse_string(slot: &mut Option<String>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.to_string());
            Ok(())
        }
        None => Err("expected a string"),
    }
}

fn parse_pointer_width(
    slot: &mut Option<PointerWidth>,
    v: Option<&str>,
) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.parse()?);
            Ok(())
        }
        _ => Err(PointerWidth::ERROR),
    }
}

fn parse_lean_mode(slot: &mut Option<LeanMode>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.parse()?);
            Ok(())
        }
        _ => Err(LeanMode::ERROR),
    }
}

fn parse_overflow(slot: &mut Option<OverflowMode>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.parse()?);
            Ok(())
        }
        _ => Err(OverflowMode::ERROR),
    }
}

fn parse_raw_deref(slot: &mut Option<RawDerefMode>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.parse()?);
            Ok(())
        }
        _ => Err(RawDerefMode::ERROR),
    }
}

fn parse_solver(slot: &mut Option<SmtSolver>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(s.parse()?);
            Ok(())
        }
        _ => Err(SmtSolver::ERROR),
    }
}

fn parse_path(slot: &mut Option<PathBuf>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(PathBuf::from(s));
            Ok(())
        }
        None => Err("expected a path"),
    }
}

fn parse_level(slot: &mut Option<Level>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(Level::from_str(s).map_err(|_| "invalid level")?);
            Ok(())
        }
        None => Err("a level"),
    }
}

fn parse_include(slot: &mut Vec<String>, v: Option<&str>) -> Result<(), &'static str> {
    if let Some(include) = v {
        slot.push(include.to_string());
    }
    Ok(())
}

fn parse_bool_value(s: &str) -> Result<bool, String> {
    decode_bool(Some(s)).map_err(|e| e.to_string())
}

fn parse_pointer_width_value(s: &str) -> Result<PointerWidth, String> {
    s.parse().map_err(|e: &'static str| e.to_string())
}

fn parse_overflow_value(s: &str) -> Result<OverflowMode, String> {
    s.parse().map_err(|e: &'static str| e.to_string())
}

fn parse_raw_deref_value(s: &str) -> Result<RawDerefMode, String> {
    s.parse().map_err(|e: &'static str| e.to_string())
}

fn parse_solver_value(s: &str) -> Result<SmtSolver, String> {
    s.parse().map_err(|e: &'static str| e.to_string())
}

fn parse_lean_value(s: &str) -> Result<LeanMode, String> {
    s.parse().map_err(|e: &'static str| e.to_string())
}

fn parse_level_value(s: &str) -> Result<Level, String> {
    Level::from_str(s).map_err(|e| e.to_string())
}

fn parse_include_value(s: &str) -> Result<IncludePattern, String> {
    IncludePattern::new(vec![s.to_string()])
}
