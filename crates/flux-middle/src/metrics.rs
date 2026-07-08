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
    )?;
    print_kvar_solution_comparison_summary()
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

pub enum TimingKind {
    /// Total time taken to run the complete Flux analysis on the crate
    Total,
    /// Time taken to check the body of a function
    CheckFn(LocalDefId),
    /// Time taken to run a single fixpoint query
    FixpointQuery(DefId, FixpointQueryKind),
    /// Time taken to generate fixes for a query
    RefinementHint(LocalDefId),
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
            TimingKind::FixpointQuery(def_id, _) => {
                timings_by_fn.entry(def_id).or_default().query += timing.duration;
            }
            TimingKind::Total => {
                // This should only appear once
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
    for timing in timings {
        match timing.kind {
            TimingKind::CheckFn(local_def_id) => {
                let def_path = tcx.def_path_str(local_def_id);
                functions.push((def_path, timing.duration));
            }
            TimingKind::FixpointQuery(def_id, kind) => {
                let key = kind.task_key(tcx, def_id);
                queries.push((key, timing.duration));
            }
            TimingKind::Total => {
                // This should only appear once
                total = timing.duration;
            }
            TimingKind::RefinementHint(_) => {
                total_reft_hint += timing.duration;
            }
        }
    }
    functions.sort_by_key(snd);
    functions.reverse();

    queries.sort_by_key(snd);
    queries.reverse();

    print_report(&functions, total, total_reft_hint);
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
                .map(|(task_key, time)| QueryTiming { task_key, time_ms: ms(time) })
                .collect(),
        },
    )
}

fn print_report(functions: &[(String, Duration)], total: Duration, total_reft_hint: Duration) {
    let stats = stats(&functions.iter().map(snd).collect_vec());
    eprintln!();
    eprintln!("───────────────────── Timing Report ────────────────────────");
    eprintln!("Total running time: {:>40}", fmt_duration(total));
    eprintln!("Total wick time:    {:>40}", fmt_duration(total_reft_hint));
    eprintln!("Functions checked:  {:>40}", stats.count);
    eprintln!("Min:                {:>40}", fmt_duration(stats.min));
    eprintln!("Max:                {:>40}", fmt_duration(stats.max));
    eprintln!("Mean:               {:>40}", fmt_duration(stats.mean));
    eprintln!("Std. Dev.:          {:>40}", fmt_duration(stats.standard_deviation));

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

// ---------------------------------------------------------------------------
// KVar solution comparison profiling
// ---------------------------------------------------------------------------

/// One entry per kvar that appeared in the body of a failing head.
#[derive(Debug, Clone)]
pub struct KvarSolutionComparison {
    /// Human-readable kvar identifier.
    pub kvar_name: String,
    /// Name of the function being checked.
    pub fn_name: String,
    /// Whether the pass-1 and pass-2 solutions are syntactically identical.
    pub same: bool,
    /// Conjuncts only in pass-1 (without wkvars) but not in pass-2 (with wkvars).
    pub before: Option<String>,
    /// Conjuncts only in pass-2 (with wkvars) but not in pass-1 (without wkvars).
    pub after: Option<String>,
    /// Pass 3: how many of pass-1's failing heads are fixed by original kvar solutions + wkvar solutions.
    pub pass3_heads_fixed: usize,
    /// Pass 3: total failing heads from pass 1.
    pub pass3_heads_total: usize,
    /// Pass 4: how many of pass-1's failing heads are fixed by kvars=TRUE + wkvar solutions.
    pub pass4_heads_fixed: usize,
    /// Pass 4: total failing heads from pass 1.
    pub pass4_heads_total: usize,
}

static KVAR_COMPARISONS: Mutex<Vec<KvarSolutionComparison>> = Mutex::new(Vec::new());

pub fn record_kvar_comparison(entry: KvarSolutionComparison) {
    KVAR_COMPARISONS.lock().unwrap().push(entry);
}

fn print_kvar_solution_comparison_summary() -> io::Result<()> {
    let comparisons = KVAR_COMPARISONS.lock().unwrap();
    let mut stderr = anstream::Stderr::always(std::io::stderr());
    let total = comparisons.len();
    let same_count = comparisons.iter().filter(|c| c.same).count();
    let diff_count = total - same_count;

    writeln!(&mut stderr, "")?;
    writeln!(&mut stderr, "{BOLD}kvar solution comparison.{BOLD:#}")?;
    writeln!(&mut stderr, "  total kvars from failing heads: {total}")?;
    writeln!(&mut stderr, "  same solution:                  {same_count}")?;
    writeln!(&mut stderr, "  different solution:             {diff_count}")?;

    // Per-head pass 3/4 stats (aggregate across all entries).
    let pass3_total_heads: usize = comparisons.iter().map(|c| c.pass3_heads_total).sum();
    let pass3_fixed_heads: usize = comparisons.iter().map(|c| c.pass3_heads_fixed).sum();
    let pass4_total_heads: usize = comparisons.iter().map(|c| c.pass4_heads_total).sum();
    let pass4_fixed_heads: usize = comparisons.iter().map(|c| c.pass4_heads_fixed).sum();
    writeln!(&mut stderr, "  pass3 (orig solutions + wkvars):")?;
    writeln!(&mut stderr, "    heads fixed / total:          {pass3_fixed_heads} / {pass3_total_heads}")?;
    writeln!(&mut stderr, "  pass4 (kvars=TRUE + wkvars):")?;
    writeln!(&mut stderr, "    heads fixed / total:          {pass4_fixed_heads} / {pass4_total_heads}")?;

    let differing: Vec<&KvarSolutionComparison> =
        comparisons.iter().filter(|c| !c.same).collect();
    if !differing.is_empty() {
        writeln!(&mut stderr, "")?;
        writeln!(&mut stderr, "{BOLD}differing kvars:{BOLD:#}")?;
        for entry in &differing {
            writeln!(&mut stderr, "  kvar {} (fn: {})", entry.kvar_name, entry.fn_name)?;
            writeln!(
                &mut stderr,
                "    only without wkvars: {}",
                entry.before.as_deref().unwrap_or("<none>")
            )?;
            writeln!(
                &mut stderr,
                "    only with wkvars:    {}",
                entry.after.as_deref().unwrap_or("<none>")
            )?;
            writeln!(
                &mut stderr,
                "    pass3 heads fixed:   {} / {}",
                entry.pass3_heads_fixed, entry.pass3_heads_total
            )?;
            writeln!(
                &mut stderr,
                "    pass4 heads fixed:   {} / {}",
                entry.pass4_heads_fixed, entry.pass4_heads_total
            )?;
        }
    }
    Ok(())
}
