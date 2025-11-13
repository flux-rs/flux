use std::{env, path::PathBuf, process, str::FromStr, sync::LazyLock};

pub use toml::Value;
use tracing::Level;

use crate::{IncludePattern, OverflowMode, PointerWidth, SmtSolver};

const FLUX_FLAG_PREFIX: &str = "-F";

/// Exit status code used for invalid flags.
pub const EXIT_FAILURE: i32 = 2;

pub struct Flags {
    /// Sets the directory to dump data. Defaults to `./log/`.
    pub log_dir: PathBuf,
    /// If present, only check files matching the [`IncludePattern`] a glob pattern.
    pub include: Option<IncludePattern>,
    /// Set the pointer size (either `32` or `64`), used to determine if an integer cast is lossy
    /// (default `64`).
    pub pointer_width: PointerWidth,
    /// If present switches on query caching and saves the cache in the provided path
    pub cache: Option<PathBuf>,
    /// Compute statistics about number and size of annotations. Dumps file to [`Self::log_dir`]
    pub annots: bool,
    /// Print statistics about time taken to analyze each fuction. Also dumps a file with the raw
    /// times for each function.
    pub timings: bool,
    /// Print statistics about number of functions checked, trusted, etc.
    pub summary: bool,
    /// Default solver. Either `z3` or `cvc5`.
    pub solver: SmtSolver,
    /// Enables qualifier scrapping in fixpoint
    pub scrape_quals: bool,
    /// Enables uninterpreted casts
    pub allow_uninterpreted_cast: bool,
    /// Translates _monomorphic_ `defs` functions into SMT `define-fun` instead of inlining them
    /// away inside `flux`.
    pub smt_define_fun: bool,
    /// If `strict` checks for over and underflow on arithmetic integer operations,
    /// If `lazy` checks for underflow and loses information if possible overflow,
    /// If `none` (default), it still checks for underflow on unsigned integer subtraction.
    pub check_overflow: OverflowMode,
    /// Dump constraints generated for each function (debugging)
    pub dump_constraint: bool,
    /// Saves the checker's trace (debugging)
    pub dump_checker_trace: Option<tracing::Level>,
    /// Saves the `fhir` for each item (debugging)
    pub dump_fhir: bool,
    /// Saves the the `fhir` (debugging)
    pub dump_rty: bool,
    /// Optimistically keeps running flux even after errors are found to get as many errors as possible
    pub catch_bugs: bool,
    /// Whether verification for the current crate is enabled. If false (the default), `flux-driver`
    /// will behave exactly like `rustc`. This flag is managed by the `cargo flux` and `flux` binaries,
    /// so you don't need to mess with it.
    pub verify: bool,
    /// If `true`, produce artifacts after analysis. This flag is managed by `cargo flux`, so you
    /// don't typically have to set it manually.
    pub full_compilation: bool,
    /// If `true`, all code is trusted by default. You can selectively untrust items by marking them with `#[trusted(no)]`. The default value of this flag is `false`, i.e., all code is untrusted by default.
    pub trusted_default: bool,
    /// If `true`, all code will be ignored by default. You can selectively unignore items by marking them with `#[ignore(no)]`. The default value of this flag is `false`, i.e., all code is unignored by default.
    pub ignore_default: bool,
    pub emit_lean_defs: bool,
    /// If `true`, every function is implicitly labeled with a `no_panic` by default.
    pub no_panic: bool,
}

impl Default for Flags {
    fn default() -> Self {
        Self {
            log_dir: PathBuf::from("./log/"),
            dump_constraint: false,
            dump_checker_trace: None,
            dump_fhir: false,
            dump_rty: false,
            catch_bugs: false,
            pointer_width: PointerWidth::default(),
            include: None,
            cache: None,
            check_overflow: OverflowMode::default(),
            scrape_quals: false,
            allow_uninterpreted_cast: false,
            solver: SmtSolver::default(),
            smt_define_fun: false,
            annots: false,
            timings: false,
            summary: true,
            verify: false,
            full_compilation: false,
            trusted_default: false,
            ignore_default: false,
            emit_lean_defs: false,
            no_panic: false,
        }
    }
}

pub(crate) static FLAGS: LazyLock<Flags> = LazyLock::new(|| {
    let mut flags = Flags::default();
    let mut includes: Vec<String> = Vec::new();
    for arg in env::args() {
        let Some((key, value)) = parse_flux_arg(&arg) else { continue };

        let result = match key {
            "log-dir" => parse_path_buf(&mut flags.log_dir, value),
            "dump-constraint" => parse_bool(&mut flags.dump_constraint, value),
            "dump-checker-trace" => parse_opt_level(&mut flags.dump_checker_trace, value),
            "dump-fhir" => parse_bool(&mut flags.dump_fhir, value),
            "dump-rty" => parse_bool(&mut flags.dump_rty, value),
            "catch-bugs" => parse_bool(&mut flags.catch_bugs, value),
            "pointer-width" => parse_pointer_width(&mut flags.pointer_width, value),
            "check-overflow" => parse_overflow(&mut flags.check_overflow, value),
            "scrape-quals" => parse_bool(&mut flags.scrape_quals, value),
            "allow-uninterpreted-cast" => parse_bool(&mut flags.allow_uninterpreted_cast, value),
            "solver" => parse_solver(&mut flags.solver, value),
            "smt-define-fun" => parse_bool(&mut flags.smt_define_fun, value),
            "annots" => parse_bool(&mut flags.annots, value),
            "timings" => parse_bool(&mut flags.timings, value),
            "summary" => parse_bool(&mut flags.summary, value),
            "cache" => parse_opt_path_buf(&mut flags.cache, value),
            "include" => parse_opt_include(&mut includes, value),
            "verify" => parse_bool(&mut flags.verify, value),
            "full-compilation" => parse_bool(&mut flags.full_compilation, value),
            "trusted" => parse_bool(&mut flags.trusted_default, value),
            "ignore" => parse_bool(&mut flags.ignore_default, value),
            "emit_lean_defs" => parse_bool(&mut flags.emit_lean_defs, value),
            "no_panic" => parse_bool(&mut flags.no_panic, value),
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

fn parse_path_buf(slot: &mut PathBuf, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = PathBuf::from(s);
            Ok(())
        }
        None => Err("a path"),
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

fn parse_overflow(slot: &mut OverflowMode, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(OverflowMode::ERROR),
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
        None => Err("a path"),
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
