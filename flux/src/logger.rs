use std::{
    fs,
    io::{self, Write},
    sync::Arc,
};

use flux_common::config::CONFIG;
use tracing::{Dispatch, Level};
use tracing_subscriber::{filter::Targets, fmt::writer::BoxMakeWriter, prelude::*, Registry};
use tracing_timing::TimingLayer;

const ONE_HUNDRED_MILLIS: u64 = 100_000_000;
const ONE_MINUTE: u64 = 60_000_000_000;

const CHECKER_FILE: &str = "checker";
const TIMINGS_FILE: &str = "timings";

pub fn install() -> io::Result<impl FnOnce() -> io::Result<()>> {
    let log_dir = &CONFIG.log_dir;

    if CONFIG.dump_checker_trace || CONFIG.dump_timings {
        fs::create_dir_all(log_dir)?;
    }

    let fmt_layer = if CONFIG.dump_checker_trace {
        let file = fs::File::create(log_dir.join(CHECKER_FILE))?;

        let writer = BoxMakeWriter::new(Arc::new(file));
        Some(
            tracing_subscriber::fmt::layer()
                .with_writer(writer)
                .json()
                .with_filter(Targets::new().with_target("flux_typeck::checker", Level::DEBUG)),
        )
    } else {
        None
    };

    let timing_layer = if CONFIG.dump_timings {
        Some(
            tracing_timing::Builder::default()
                .layer(|| {
                    tracing_timing::Histogram::new_with_bounds(ONE_HUNDRED_MILLIS, ONE_MINUTE, 3)
                        .unwrap()
                })
                .with_filter(
                    Targets::new()
                        .with_target("flux_typeck::checker", Level::DEBUG)
                        .with_target("flux_typeck::fixpoint", Level::DEBUG),
                ),
        )
    } else {
        None
    };

    let dispatch = Dispatch::new(Registry::default().with(fmt_layer).with(timing_layer));

    dispatch.clone().init();

    Ok(move || {
        if CONFIG.dump_timings {
            let mut file = fs::File::create(log_dir.join(TIMINGS_FILE))?;
            let mut file_contents = String::new();
            let timing_layer = dispatch.downcast_ref::<TimingLayer>().unwrap();
            timing_layer.force_synchronize();
            timing_layer.with_histograms(|spans_map| {
                for (span_name, events_map) in spans_map {
                    let mut total_time = 0;
                    for (_event_name, event_histogram) in events_map {
                        event_histogram.refresh();
                        for iteration_value in event_histogram.iter_recorded() {
                            total_time += iteration_value.value_iterated_to();
                        }
                    }
                    let message =
                        format!("{}: total time {}ms\n", span_name, total_time / 1_000_000);
                    file_contents += &message;
                }
            });
            file.write_all(file_contents.as_bytes())
        } else {
            Ok(())
        }
    })
}
