use std::{
    fs, io,
    sync::Mutex,
    time::{Duration, Instant},
};

use flux_config as config;
use itertools::Itertools;
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

use crate::FixpointQueryKind;

static TIMINGS: Mutex<Vec<Entry>> = Mutex::new(Vec::new());

pub enum TimingKind {
    /// Time taken to check the body of a function
    CheckFn(LocalDefId),
    /// Time taken to run a single fixpoint query
    FixpointQuery(DefId, FixpointQueryKind),
}

pub fn enter<R>(tcx: TyCtxt, f: impl FnOnce() -> R) -> R {
    if !config::timings() {
        return f();
    }
    let start = Instant::now();
    let r = f();
    print_and_dump_report(tcx, start.elapsed(), std::mem::take(&mut *TIMINGS.lock().unwrap()))
        .unwrap();
    r
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

fn print_and_dump_report(tcx: TyCtxt, total: Duration, timings: Vec<Entry>) -> io::Result<()> {
    let mut functions = vec![];
    let mut queries = vec![];
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
        }
    }
    functions.sort_by_key(snd);
    functions.reverse();

    queries.sort_by_key(snd);
    queries.reverse();

    print_report(&functions, total);
    dump_timings(tcx, TimingsDump {
        total: ms(total),
        functions: functions
            .into_iter()
            .map(|(def_path, time)| FuncTiming { def_path, time_ms: ms(time) })
            .collect(),
        queries: queries
            .into_iter()
            .map(|(task_key, time)| QueryTiming { task_key, time_ms: ms(time) })
            .collect(),
    })
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

fn stats(durations: &[Duration]) -> Stats {
    let count = durations.len() as u32;
    if count == 0 {
        return Stats::default();
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

    Stats { count, max, min, mean, standard_deviation }
}

#[derive(Default)]
struct Stats {
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
        format!("{}ns", nanos)
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
            format!("{}m {}s", minutes, seconds_remainder)
        } else {
            let hours = minutes / 60;
            let minutes_remainder = minutes % 60;

            if hours < 24 {
                format!("{}h {}m {}s", hours, minutes_remainder, seconds_remainder)
            } else {
                let days = hours / 24;
                let hours_remainder = hours % 24;
                format!(
                    "{}d {}h {}m {}s",
                    days, hours_remainder, minutes_remainder, seconds_remainder
                )
            }
        }
    }
}
