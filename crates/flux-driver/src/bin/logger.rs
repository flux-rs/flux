use std::{fs, io, sync::Arc};

use flux_config as config;
use tracing::{Dispatch, Level};
use tracing_subscriber::{Registry, filter::Targets, fmt::writer::BoxMakeWriter, prelude::*};

const CHECKER_FILE: &str = "checker";

pub fn install() -> io::Result<()> {
    if config::dump_checker_trace() {
        let log_dir = config::log_dir();
        fs::create_dir_all(log_dir)?;
        let file = fs::File::create(log_dir.join(CHECKER_FILE))?;
        let writer = BoxMakeWriter::new(Arc::new(file));
        let fmt_layer = tracing_subscriber::fmt::layer()
            .with_writer(writer)
            .json()
            .with_filter(
                Targets::new()
                    .with_target("flux_refineck::checker", Level::DEBUG)
                    .with_target("flux_driver::collector", Level::DEBUG)
            );
        let dispatch = Dispatch::new(Registry::default().with(fmt_layer));
        dispatch.clone().init();
    }
    Ok(())
}
