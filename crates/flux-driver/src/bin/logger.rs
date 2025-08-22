use std::{fs, io, sync::Arc};

use flux_config as config;
use tracing::Dispatch;
use tracing_subscriber::{Registry, filter::Targets, fmt::writer::BoxMakeWriter, prelude::*};

const CHECKER_FILE: &str = "checker";

pub fn install() -> io::Result<()> {
    if let Some(level) = config::dump_checker_trace() {
        let log_dir = config::log_dir();
        fs::create_dir_all(log_dir)?;
        let file = fs::File::create(log_dir.join(CHECKER_FILE))?;
        let writer = BoxMakeWriter::new(Arc::new(file));
        let fmt_layer = tracing_subscriber::fmt::layer()
            .with_writer(writer)
            .json()
            .with_filter(
                Targets::new().with_default(level), // This will capture all WARN, ERROR events from any module
                                                    // .with_target("flux_refineck::checker", level)
                                                    // .with_target("flux_driver::collector", Level::WARN)
                                                    // .with_target("flux_fhir_analysis::conv", Level::WARN),
            );
        let dispatch = Dispatch::new(Registry::default().with(fmt_layer));
        dispatch.clone().init();
    }
    Ok(())
}
