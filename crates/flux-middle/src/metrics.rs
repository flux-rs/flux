use std::{
    collections::HashMap,
    fs,
    io::{self, Write as _},
    sync::{Mutex, atomic::AtomicU32},
    time::{Duration, Instant},
};

use flux_config as config;
use itertools::Itertools;
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

use crate::FixpointQueryKind;

const BOLD: anstyle::Style = anstyle::Style::new().bold();
const GREY: anstyle::Style = anstyle::AnsiColor::BrightBlack.on_default();

pub fn print_summary(total_time: Duration) -> io::Result<()> {
    let mut stderr = anstream::Stderr::always(std::io::stderr());
    writeln!(
        &mut stderr,
        "{BOLD}summary.{BOLD:#} {} functions processed: {} checked; {} trusted; {} ignored. {} constraints solved. Finished in {}{GREY:#}",
        METRICS.get(Metric::FnTotal),
        METRICS.get(Metric::FnChecked),
        METRICS.get(Metric::FnTrusted),
        METRICS.get(Metric::FnIgnored),
        METRICS.get(Metric::CsTotal),
        fmt_duration(total_time),
    )
}

static METRICS: Metrics = Metrics::new();

#[repr(u8)]
pub enum Metric {
    /// number of functions (i.e., `DefId`s) processed
    FnTotal,
    /// number of "trusted" functions
    FnTrusted,
    /// number of "ignored" functions
    FnIgnored,
    /// number of functions that were actually checked
    FnChecked,
    /// number of cached queries
    FnCached,
    /// number of trivial queries
    FnTrivial,
    /// number of concrete constraints
    CsTotal,
    /// number of unsat constraints
    CsError,
}

struct Metrics {
    counts: [AtomicU32; 8],
}

impl Metrics {
    const fn new() -> Self {
        Self {
            counts: [
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
                AtomicU32::new(0),
            ],
        }
    }

    fn incr(&self, metric: Metric, val: u32) {
        self.counts[metric as usize].fetch_add(val, std::sync::atomic::Ordering::Relaxed);
    }

    fn get(&self, metric: Metric) -> u32 {
        self.counts[metric as usize].load(std::sync::atomic::Ordering::Relaxed)
    }
}

pub fn incr_metric(metric: Metric, val: u32) {
    METRICS.incr(metric, val);
}

pub fn incr_metric_if(cond: bool, metric: Metric) {
    if cond {
        incr_metric(metric, 1);
    }
}

static TIMINGS: Mutex<Vec<Entry>> = Mutex::new(Vec::new());
static COMPARISONS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());

#[derive(Serialize)]
pub struct ItemIdentity {
    pub crate_name: String,
    pub def_path: String,
    pub name: String,
}

impl ItemIdentity {
    pub fn new(tcx: TyCtxt, def_id: DefId) -> Self {
        Self {
            crate_name: tcx.crate_name(def_id.krate).to_string(),
            def_path: tcx.def_path_str(def_id),
            name: tcx
                .opt_item_name(def_id)
                .map_or_else(|| tcx.def_path_str(def_id), |name| name.to_string()),
        }
    }
}

pub fn record_comparison(
    mut comparison: serde_json::Value,
    artifacts: Vec<(String, String)>,
) -> io::Result<()> {
    if config::timings() {
        let mut comparisons = COMPARISONS.lock().unwrap();
        let invocation = comparisons.len();
        comparison["identity"]["invocation"] = invocation.into();
        let crate_name = comparison["identity"]["crate_name"].as_str().unwrap();
        let directory = format!("{crate_name}-comparison-artifacts/{invocation}");
        fs::create_dir_all(config::log_dir().join(&directory))?;
        let mut references = serde_json::Map::new();
        for (name, contents) in artifacts {
            let relative_path = format!("{directory}/{name}");
            fs::write(config::log_dir().join(&relative_path), contents)?;
            references.insert(name, relative_path.into());
        }
        comparison["artifacts"] = references.into();
        comparisons.push(comparison);
    }
    Ok(())
}

pub enum TimingKind {
    /// Total time taken to run the complete Flux analysis on the crate
    Total,
    /// Time taken to check the body of a function
    CheckFn(LocalDefId),
    /// Time taken to run a single fixpoint query
    FixpointQuery(DefId, FixpointQueryKind, bool),
    /// Time taken to generate fixes for a query
    RefinementHint(LocalDefId),
    /// Stats for a CHC that fixpoint failed to verify: hornspec outcome, timing,
    /// and how many of its errors wick/hornspec found solutions for.
    FailedCHCStats {
        def_id: DefId,
        outcome: HornspecOutcome,
        /// Total errors fixpoint reported for this CHC
        error_count: usize,
        /// Errors for which wick found at least one solution
        wick_solved: usize,
        /// Errors covered by hornspec (error_count if hornspec said safe, else 0)
        hornspec_solved: usize,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HornspecOutcome {
    Safe,
    Unsafe,
    Timeout,
}

#[derive(Serialize)]
struct TimingsDump {
    /// Total time taken to run the complte Flux analysis on the crate
    total: ms,
    /// Per-function analysis timings
    functions: Vec<FuncTiming>,
    /// Per-query execution timings
    queries: Vec<QueryTiming>,
}

#[derive(Serialize)]
struct FuncTiming {
    def_path: String,
    time_ms: ms,
}

#[derive(Serialize)]
struct QueryTiming {
    task_key: String,
    time_ms: ms,
    used_by_wick: bool,
}

fn snd<A, B: Copy>(&(_, b): &(A, B)) -> B {
    b
}

#[derive(Default, Debug, Clone)]
pub struct FnTiming {
    pub query: Duration,
    pub reft_hint: Duration,
    pub iters: usize,
}

pub fn refinement_hint_timings() -> (HashMap<DefId, FnTiming>, Duration) {
    let mut total = Duration::from_secs(0);
    let mut timings_by_fn: HashMap<_, FnTiming> = HashMap::default();
    for timing in TIMINGS.lock().unwrap().iter() {
        match timing.kind {
            TimingKind::RefinementHint(fn_def_id) => {
                let timings = timings_by_fn.entry(fn_def_id.to_def_id()).or_default();
                timings.reft_hint += timing.duration;
                timings.iters += 1;
            }
            TimingKind::FixpointQuery(def_id, _, _) => {
                timings_by_fn.entry(def_id).or_default().query += timing.duration;
            }
            TimingKind::Total => {
                total = timing.duration;
            }
            _ => {}
        }
    }
    (timings_by_fn, total)
}

pub fn print_and_dump_timings(tcx: TyCtxt) -> io::Result<()> {
    if !config::timings() {
        return Ok(());
    }

    let timings = std::mem::take(&mut *TIMINGS.lock().unwrap());
    let mut functions = vec![];
    let mut queries = vec![];
    let mut total = Duration::from_secs(0);
    let mut total_reft_hint = Duration::from_secs(0);
    let mut total_fixpoint = Duration::ZERO;
    let mut wick_fixpoint = Duration::ZERO;
    let mut hornspec_durations: Vec<Duration> = vec![];
    let mut hornspec_safe: u32 = 0;
    let mut hornspec_timeout: u32 = 0;
    let mut hornspec_timeout_errors: usize = 0;
    let mut hornspec_total_errors: usize = 0;
    let mut hornspec_solved_errors: usize = 0;
    let mut hornspec_wick_no_hornspec_errors: usize = 0;
    let mut hornspec_hornspec_no_wick_errors: usize = 0;
    let mut wick_solved_errors: usize = 0;
    for timing in timings {
        match timing.kind {
            TimingKind::CheckFn(local_def_id) => {
                let def_path = tcx.def_path_str(local_def_id);
                functions.push((def_path, timing.duration));
            }
            TimingKind::FixpointQuery(def_id, kind, used_by_wick) => {
                total_fixpoint += timing.duration;
                if used_by_wick {
                    wick_fixpoint += timing.duration;
                }
                let key = kind.task_key(tcx, def_id);
                queries.push((key, timing.duration, used_by_wick));
            }
            TimingKind::Total => {
                total = timing.duration;
            }
            TimingKind::RefinementHint(_) => {
                total_reft_hint += timing.duration;
            }
            TimingKind::FailedCHCStats {
                outcome,
                error_count,
                wick_solved,
                hornspec_solved,
                ..
            } => {
                if hornspec_solved > wick_solved {
                    hornspec_hornspec_no_wick_errors += hornspec_solved - wick_solved;
                } else {
                    hornspec_wick_no_hornspec_errors += wick_solved - hornspec_solved;
                }
                hornspec_durations.push(timing.duration);
                hornspec_total_errors += error_count;
                wick_solved_errors += wick_solved;
                hornspec_solved_errors += hornspec_solved;
                match outcome {
                    HornspecOutcome::Safe => hornspec_safe += 1,
                    HornspecOutcome::Timeout => {
                        hornspec_timeout += 1;
                        hornspec_timeout_errors += error_count;
                    }
                    HornspecOutcome::Unsafe => {}
                }
            }
        }
    }
    functions.sort_by_key(snd);
    functions.reverse();

    queries.sort_by_key(|query| query.1);
    queries.reverse();

    print_report(
        &functions,
        total,
        total_reft_hint,
        total_fixpoint,
        wick_fixpoint,
        &hornspec_durations,
        hornspec_safe,
        hornspec_timeout,
        hornspec_timeout_errors,
        hornspec_total_errors,
        hornspec_solved_errors,
        wick_solved_errors,
        hornspec_hornspec_no_wick_errors,
        hornspec_wick_no_hornspec_errors,
    );
    let total_hornspec: Duration = hornspec_durations.iter().sum();
    let function_stats = stats(&functions.iter().map(snd).collect_vec());
    let summary = serde_json::json!({
        "schema_version": 1,
        "identity": { "crate_name": tcx.crate_name(LOCAL_CRATE).to_string() },
        "timing": {
            "total_ms": ms(total),
            "wick_ms": ms(total_reft_hint),
            "fixpoint_ms": ms(total_fixpoint),
            "wick_fixpoint_ms": ms(wick_fixpoint),
            "functions": {
                "count": function_stats.count,
                "min_ms": ms(function_stats.min),
                "max_ms": ms(function_stats.max),
                "mean_ms": ms(function_stats.mean),
                "std_dev_ms": ms(function_stats.standard_deviation),
                "top_5": functions.iter().take(5).map(|(def_path, time)| {
                    serde_json::json!({ "identity": { "def_path": def_path }, "time_ms": ms(*time) })
                }).collect_vec(),
            },
        },
        "functions": {
            "total": METRICS.get(Metric::FnTotal),
            "checked": METRICS.get(Metric::FnChecked),
            "trusted": METRICS.get(Metric::FnTrusted),
            "ignored": METRICS.get(Metric::FnIgnored),
            "cached": METRICS.get(Metric::FnCached),
            "trivial": METRICS.get(Metric::FnTrivial),
        },
        "constraints": {
            "total": METRICS.get(Metric::CsTotal),
            "errors": METRICS.get(Metric::CsError),
        },
        "comparison": {
            "queries": hornspec_durations.len(),
            "failing_chcs": hornspec_total_errors,
            "hornspec": {
                "configuration": {
                    "timeout_seconds": config::hornspec_timeout(),
                    "skip_maximal": config::hornspec_skip_maximal(),
                },
                "safe_queries": hornspec_safe,
                "unsafe_queries": hornspec_durations.len() - hornspec_safe as usize - hornspec_timeout as usize,
                "timeout_queries": hornspec_timeout,
                "timeout_chcs": hornspec_timeout_errors,
                "solved_chcs": hornspec_solved_errors,
                "solved_without_wick_chcs": hornspec_hornspec_no_wick_errors,
                "total_ms": ms(total_hornspec),
                "mean_ms": if hornspec_durations.is_empty() { None } else {
                    Some(ms(total_hornspec / hornspec_durations.len() as u32))
                },
            },
            "wick": {
                "solved_chcs": wick_solved_errors,
                "solved_without_hornspec_chcs": hornspec_wick_no_hornspec_errors,
            },
        },
    });
    fs::create_dir_all(config::log_dir())?;
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let mut file = fs::File::create(config::log_dir().join(format!("{crate_name}-metrics.json")))?;
    serde_json::to_writer_pretty(&mut file, &summary)?;
    let mut file = fs::File::create(
        config::log_dir().join(format!("{crate_name}-hornspec-comparison.jsonl")),
    )?;
    for comparison in std::mem::take(&mut *COMPARISONS.lock().unwrap()) {
        serde_json::to_writer(&mut file, &comparison)?;
        writeln!(file)?;
    }
    dump_timings(
        tcx,
        TimingsDump {
            total: ms(total),
            functions: functions
                .into_iter()
                .map(|(def_path, time)| FuncTiming { def_path, time_ms: ms(time) })
                .collect(),
            queries: queries
                .into_iter()
                .map(|(task_key, time, used_by_wick)| {
                    QueryTiming { task_key, time_ms: ms(time), used_by_wick }
                })
                .collect(),
        },
    )
}

fn print_report(
    functions: &[(String, Duration)],
    total: Duration,
    total_reft_hint: Duration,
    total_fixpoint: Duration,
    wick_fixpoint: Duration,
    hornspec_durations: &[Duration],
    hornspec_safe: u32,
    hornspec_timeout: u32,
    hornspec_timeout_errors: usize,
    hornspec_total_errors: usize,
    hornspec_solved_errors: usize,
    wick_solved_errors: usize,
    hornspec_no_wick_errors: usize,
    wick_no_hornspec_errors: usize,
) {
    let stats = stats(&functions.iter().map(snd).collect_vec());
    eprintln!();
    eprintln!("───────────────────── Timing Report ────────────────────────");
    eprintln!("Total running time: {:>40}", fmt_duration(total));
    eprintln!("Total wick time:    {:>40}", fmt_duration(total_reft_hint));
    eprintln!("Total fixpoint time:{:>40}", fmt_duration(total_fixpoint));
    eprintln!("Fixpoint for Wick:  {:>40}", fmt_duration(wick_fixpoint));
    eprintln!("Wick + fixpoint:    {:>40}", fmt_duration(total_reft_hint + wick_fixpoint));
    eprintln!("Functions checked:  {:>40}", stats.count);
    eprintln!("Min:                {:>40}", fmt_duration(stats.min));
    eprintln!("Max:                {:>40}", fmt_duration(stats.max));
    eprintln!("Mean:               {:>40}", fmt_duration(stats.mean));
    eprintln!("Std. Dev.:          {:>40}", fmt_duration(stats.standard_deviation));

    if !hornspec_durations.is_empty() {
        let total_hornspec: Duration = hornspec_durations.iter().sum();
        let mean_hornspec = total_hornspec / hornspec_durations.len() as u32;
        eprintln!("────────────────────────────────────────────────────────────");
        eprintln!(
            "Hornspec safe:      {:>40}",
            format!("{hornspec_safe}/{}", hornspec_durations.len())
        );
        if hornspec_timeout > 0 {
            eprintln!("Hornspec timeouts:  {:>40}", hornspec_timeout);
            eprintln!("Hornspec timeouts (CHCs):{:>40}", hornspec_timeout_errors);
        }
        eprintln!("Hornspec errors:    {:>40}", hornspec_total_errors);
        eprintln!(
            "Hornspec solved:    {:>40}",
            format!("{hornspec_solved_errors}/{hornspec_total_errors}"),
        );
        eprintln!("Hornspec solved (NO Wick):{:>40}", format!("{hornspec_no_wick_errors}"),);
        eprintln!(
            "Wick solved:        {:>40}",
            format!("{wick_solved_errors}/{hornspec_total_errors}"),
        );
        eprintln!("Wick solved (NO Hornspec):{:>40}", format!("{wick_no_hornspec_errors}"),);
        eprintln!("Hornspec total:     {:>40}", fmt_duration(total_hornspec));
        eprintln!("Hornspec mean:      {:>40}", fmt_duration(mean_hornspec));
    }

    let top5 = functions.iter().take(5).cloned().collect_vec();
    if !top5.is_empty() {
        eprintln!("────────────────────────────────────────────────────────────");
        eprintln!("Top 5 Functions ");
        for (def_path, duration) in top5 {
            let len = def_path.len();
            if len > 46 {
                eprintln!(
                    "• …{} {:>width$}",
                    &def_path[len - 46..],
                    fmt_duration(duration),
                    width = 10
                );
            } else {
                eprintln!(
                    "• {def_path} {:>width$}",
                    fmt_duration(duration),
                    width = 60 - def_path.len() - 3
                );
            }
        }
    }
    eprintln!("────────────────────────────────────────────────────────────");
}

fn dump_timings(tcx: TyCtxt, timings: TimingsDump) -> io::Result<()> {
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    fs::create_dir_all(config::log_dir())?;
    let path = config::log_dir().join(format!("{crate_name}-timings.json"));
    let mut file = fs::File::create(path)?;
    serde_json::to_writer(&mut file, &timings)?;
    Ok(())
}

pub fn time_it<R>(kind: TimingKind, f: impl FnOnce() -> R) -> R {
    if !config::timings() {
        return f();
    }
    let start = Instant::now();
    let r = f();
    TIMINGS
        .lock()
        .unwrap()
        .push(Entry { duration: start.elapsed(), kind });
    r
}

/// Record a pre-timed entry directly. Useful when the kind depends on the
/// result of the computation (e.g. HornspecQuery carries `safe: bool`).
pub fn record(kind: TimingKind, duration: Duration) {
    if !config::timings() {
        return;
    }
    TIMINGS.lock().unwrap().push(Entry { duration, kind });
}

fn stats(durations: &[Duration]) -> TimingStats {
    let count = durations.len() as u32;
    if count == 0 {
        return TimingStats::default();
    }
    let sum: Duration = durations.iter().sum();
    let mean = sum / count;

    let meanf = mean.as_millis() as f64;
    let mut sum_of_squares = 0.0;
    let mut max = Duration::ZERO;
    let mut min = Duration::MAX;
    for duration in durations {
        let diff = duration.as_millis() as f64 - meanf;
        sum_of_squares += diff * diff;
        max = max.max(*duration);
        min = min.min(*duration);
    }
    let standard_deviation = Duration::from_millis((sum_of_squares / count as f64).sqrt() as u64);

    TimingStats { count, max, min, mean, standard_deviation }
}

#[derive(Default)]
struct TimingStats {
    count: u32,
    max: Duration,
    min: Duration,
    mean: Duration,
    standard_deviation: Duration,
}

struct Entry {
    duration: Duration,
    kind: TimingKind,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Serialize)]
#[serde(into = "u128")]
struct ms(Duration);

impl From<ms> for u128 {
    fn from(value: ms) -> Self {
        value.0.as_millis()
    }
}

fn fmt_duration(duration: Duration) -> String {
    let nanos = duration.as_nanos();

    if nanos < 1_000 {
        format!("{nanos}ns")
    } else if nanos < 1_000_000 {
        format!("{:.2}µs", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2}ms", nanos as f64 / 1_000_000.0)
    } else if nanos < 60_000_000_000 {
        format!("{:.2}s", nanos as f64 / 1_000_000_000.0)
    } else {
        let seconds = duration.as_secs();
        let minutes = seconds / 60;
        let seconds_remainder = seconds % 60;

        if minutes < 60 {
            format!("{minutes}m {seconds_remainder}s")
        } else {
            let hours = minutes / 60;
            let minutes_remainder = minutes % 60;

            if hours < 24 {
                format!("{hours}h {minutes_remainder}m {seconds_remainder}s")
            } else {
                let days = hours / 24;
                let hours_remainder = hours % 24;
                format!("{days}d {hours_remainder}h {minutes_remainder}m {seconds_remainder}s",)
            }
        }
    }
}
