use std::{
    fs,
    io::{self, Write},
    sync::Arc,
};

use flux_config as config;
use tracing::{Dispatch, Level};
use tracing_subscriber::{filter::Targets, fmt::writer::BoxMakeWriter, prelude::*, Registry};
use tracing_timing::TimingLayer;

const ONE_MILLIS: u64 = 1_000_000;
const ONE_MINUTE: u64 = 60_000_000_000;

const CHECKER_FILE: &str = "checker";
const TIMINGS_FILE: &str = "timings";

fn ns_to_ms(timing_ns: u64) -> f64 {
    (timing_ns as f64) / 1_000_000.0
}

pub fn install() -> io::Result<impl FnOnce() -> io::Result<()>> {
    let log_dir = config::log_dir();

    if config::dump_checker_trace() || config::dump_timings() {
        fs::create_dir_all(log_dir)?;
    }

    let mut fmt_layer = None;
    if config::dump_checker_trace() {
        let file = fs::File::create(log_dir.join(CHECKER_FILE))?;

        let writer = BoxMakeWriter::new(Arc::new(file));
        fmt_layer = Some(
            tracing_subscriber::fmt::layer()
                .with_writer(writer)
                .json()
                .with_filter(Targets::new().with_target("flux_refineck::checker", Level::DEBUG)),
        );
    }

    let mut timing_layer = None;
    if config::dump_timings() {
        timing_layer = Some(
            tracing_timing::Builder::default()
                .no_span_recursion()
                .layer(|| {
                    tracing_timing::Histogram::new_with_bounds(ONE_MILLIS, ONE_MINUTE, 3).unwrap()
                })
                .with_filter(
                    Targets::new()
                        .with_target("flux_refineck", Level::INFO)
                        .with_target("flux_driver::callbacks", Level::INFO),
                ),
        );
    };

    let dispatch = Dispatch::new(Registry::default().with(fmt_layer).with(timing_layer));

    dispatch.clone().init();

    Ok(move || {
        if config::dump_timings() {
            let mut file = fs::File::create(log_dir.join(TIMINGS_FILE))?;
            let timing_layer = dispatch.downcast_ref::<TimingLayer>().unwrap();
            timing_layer.force_synchronize();
            timing_layer.with_histograms(|spans_map| {
                for (span_name, events_map) in spans_map {
                    let mut span_time_ns = 0;
                    writeln!(file, "{span_name}")?;
                    for (event_name, event_histogram) in events_map {
                        event_histogram.refresh();

                        let event_time_ns = event_histogram
                            .iter_recorded()
                            .map(|v| v.value_iterated_to())
                            .sum();

                        writeln!(file, "  {event_name}")?;
                        writeln!(file, "    num events:   {}", event_histogram.len())?;
                        writeln!(
                            file,
                            "    min non-zero: {:.2}ms",
                            ns_to_ms(event_histogram.min_nz())
                        )?;
                        writeln!(
                            file,
                            "    1st quartile: {:.2}ms",
                            ns_to_ms(event_histogram.value_at_quantile(0.25))
                        )?;
                        writeln!(
                            file,
                            "    2nd quartile: {:.2}ms",
                            ns_to_ms(event_histogram.value_at_quantile(0.50))
                        )?;
                        writeln!(
                            file,
                            "    3rd quartile: {:.2}ms",
                            ns_to_ms(event_histogram.value_at_quantile(0.75))
                        )?;
                        writeln!(
                            file,
                            "    max:          {:.2}ms",
                            ns_to_ms(event_histogram.max())
                        )?;
                        writeln!(file, "    total time:   {:.2}ms", ns_to_ms(event_time_ns))?;
                        span_time_ns += event_time_ns;
                    }
                    write!(file, "total time: {:.2}ms\n\n", ns_to_ms(span_time_ns))?;
                }
                Ok(())
            })
        } else {
            Ok(())
        }
    })
}
