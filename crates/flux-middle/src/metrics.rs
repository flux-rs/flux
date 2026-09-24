use std::{
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

#[cfg(feature = "suggestions")]
static SUGGESTION_COMPARISONS: Mutex<Vec<liquid_fixpoint::SuggestionComparisonEvent>> =
    Mutex::new(Vec::new());

#[cfg(feature = "suggestions")]
pub fn record_suggestion_comparison(comparison: liquid_fixpoint::SuggestionComparisonEvent) {
    SUGGESTION_COMPARISONS.lock().unwrap().push(comparison);
}

#[cfg(feature = "suggestions")]
pub fn print_suggestion_comparison_summary() -> io::Result<()> {
    let comparisons = std::mem::take(&mut *SUGGESTION_COMPARISONS.lock().unwrap());
    if comparisons.is_empty() {
        return Ok(());
    }

    let stderr = &mut anstream::Stderr::always(std::io::stderr());
    writeln!(stderr, "\nsuggestions-z3 comparison report")?;
    let all = comparisons.iter().collect_vec();
    print_comparison_summary(stderr, "all operations", &all)?;
    for (operation, name) in [
        (liquid_fixpoint::SuggestionComparisonOperation::Qe, "QE"),
        (liquid_fixpoint::SuggestionComparisonOperation::Validity, "validity"),
    ] {
        let entries = comparisons
            .iter()
            .filter(|entry| entry.operation == operation)
            .collect_vec();
        print_comparison_summary(stderr, name, &entries)?;
    }

    let mismatches = comparisons
        .iter()
        .filter(|entry| {
            entry.outcome == liquid_fixpoint::SuggestionComparisonOutcome::Different
                || entry.outcome == liquid_fixpoint::SuggestionComparisonOutcome::ProcessFailed
        })
        .collect_vec();
    if !mismatches.is_empty() {
        writeln!(
            stderr,
            "semantic mismatches (both succeeded, results differed) ({}):",
            mismatches.len()
        )?;
        for (index, mismatch) in mismatches.into_iter().enumerate() {
            let operation = match mismatch.operation {
                liquid_fixpoint::SuggestionComparisonOperation::Qe => "QE",
                liquid_fixpoint::SuggestionComparisonOperation::Validity => "validity",
            };
            writeln!(stderr, "  mismatch {} [{operation}]", index + 1)?;
            if let Some(details) = &mismatch.details {
                for line in details.lines() {
                    writeln!(stderr, "    {line}")?;
                }
            }
        }
    }
    Ok(())
}

#[cfg(feature = "suggestions")]
fn print_comparison_summary(
    out: &mut impl io::Write,
    name: &str,
    entries: &[&liquid_fixpoint::SuggestionComparisonEvent],
) -> io::Result<()> {
    use liquid_fixpoint::SuggestionComparisonOutcome as Outcome;

    let count = |outcome| {
        entries
            .iter()
            .filter(|entry| entry.outcome == outcome)
            .count()
    };
    writeln!(
        out,
        "  {name}: {} comparisons; mismatches {}; process-only failures {}; bindings-only failures {}; semantic mismatches {}; both failed {}; agreed {}; comparison failed {}",
        entries.len(),
        count(Outcome::Different) + count(Outcome::ProcessFailed) + count(Outcome::BindingsFailed),
        count(Outcome::ProcessFailed),
        count(Outcome::BindingsFailed),
        count(Outcome::Different),
        count(Outcome::BothFailed),
        count(Outcome::Agreed),
        count(Outcome::ComparisonFailed),
    )?;

    if entries.is_empty() {
        writeln!(out, "    total time: bindings 0ns; process 0ns")?;
        writeln!(out, "    process-bindings time delta: n/a")?;
        return Ok(());
    }

    let bindings_total = entries
        .iter()
        .map(|entry| entry.bindings_time)
        .sum::<Duration>();
    let process_total = entries
        .iter()
        .map(|entry| entry.process_time)
        .sum::<Duration>();
    writeln!(
        out,
        "    total time: bindings {}; process {}",
        fmt_duration(bindings_total),
        fmt_duration(process_total),
    )?;

    let mut deltas = entries
        .iter()
        .map(|entry| entry.process_time.as_nanos() as i128 - entry.bindings_time.as_nanos() as i128)
        .collect_vec();
    deltas.sort_unstable();
    let min = deltas[0];
    let max = deltas[deltas.len() - 1];
    let avg = deltas.iter().sum::<i128>() / deltas.len() as i128;
    writeln!(
        out,
        "    process-bindings time delta (n={}): min {}, max {}, avg {}",
        deltas.len(),
        fmt_signed_duration(min),
        fmt_signed_duration(max),
        fmt_signed_duration(avg),
    )
}

#[cfg(feature = "suggestions")]
fn fmt_signed_duration(nanos: i128) -> String {
    let sign = if nanos < 0 { "-" } else { "+" };
    let nanos = nanos.unsigned_abs();
    if nanos < 1_000 {
        format!("{sign}{nanos}ns")
    } else if nanos < 1_000_000 {
        format!("{sign}{:.2}us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{sign}{:.2}ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{sign}{:.2}s", nanos as f64 / 1_000_000_000.0)
    }
}

#[cfg(all(test, feature = "suggestions"))]
mod suggestion_comparison_tests {
    use liquid_fixpoint::{
        SuggestionComparisonOperation as Operation, SuggestionComparisonOutcome as Outcome,
    };

    use super::*;

    #[test]
    fn comparison_summary_counts_outcomes_and_signed_deltas() {
        let entries = vec![
            liquid_fixpoint::SuggestionComparisonEvent {
                operation: Operation::Qe,
                outcome: Outcome::Agreed,
                bindings_time: Duration::from_millis(10),
                process_time: Duration::from_millis(8),
                details: None,
            },
            liquid_fixpoint::SuggestionComparisonEvent {
                operation: Operation::Qe,
                outcome: Outcome::Different,
                bindings_time: Duration::from_millis(4),
                process_time: Duration::from_millis(10),
                details: Some("fixture mismatch".to_string()),
            },
        ];
        let entries = entries.iter().collect_vec();
        let mut output = Vec::new();
        print_comparison_summary(&mut output, "QE", &entries).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("2 comparisons; mismatches 1"));
        assert!(output.contains("total time: bindings 14.00ms; process 18.00ms"));
        assert!(output.contains("min -2.00ms, max +6.00ms, avg +2.00ms"));
    }

    #[test]
    fn comparison_summary_separates_mismatches_from_inconclusive_runs() {
        let entries = [
            Outcome::Different,
            Outcome::ProcessFailed,
            Outcome::BindingsFailed,
            Outcome::BothFailed,
            Outcome::ComparisonFailed,
        ]
        .map(|outcome| {
            liquid_fixpoint::SuggestionComparisonEvent {
                operation: Operation::Validity,
                outcome,
                bindings_time: Duration::ZERO,
                process_time: Duration::ZERO,
                details: None,
            }
        });
        let entries = entries.iter().collect_vec();
        let mut output = Vec::new();
        print_comparison_summary(&mut output, "validity", &entries).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("5 comparisons; mismatches 3; process-only failures 1; bindings-only failures 1; semantic mismatches 1; both failed 1; agreed 0; comparison failed 1"));
    }
}

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

pub enum TimingKind {
    /// Total time taken to run the complete Flux analysis on the crate
    Total,
    /// Time taken to check the body of a function
    CheckBody(LocalDefId),
    /// Time taken to run a single fixpoint query
    FixpointQuery(DefId, FixpointQueryKind),
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

pub fn print_and_dump_timings(tcx: TyCtxt) -> io::Result<()> {
    if !config::timings() {
        return Ok(());
    }

    let timings = std::mem::take(&mut *TIMINGS.lock().unwrap());
    let mut functions = vec![];
    let mut queries = vec![];
    let mut total = Duration::from_secs(0);
    for timing in timings {
        match timing.kind {
            TimingKind::CheckBody(local_def_id) => {
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
        }
    }
    functions.sort_by_key(snd);
    functions.reverse();

    queries.sort_by_key(snd);
    queries.reverse();

    print_report(&functions, total);
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

fn print_report(functions: &[(String, Duration)], total: Duration) {
    let stats = stats(&functions.iter().map(snd).collect_vec());
    eprintln!();
    eprintln!("───────────────────── Timing Report ────────────────────────");
    eprintln!("Total running time: {:>40}", fmt_duration(total));
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
