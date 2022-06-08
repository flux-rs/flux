use std::{fs, io, sync::Arc};

use flux_common::config::CONFIG;
use tracing::Level;
use tracing_subscriber::{filter::Targets, fmt::writer::BoxMakeWriter, prelude::*, Registry};

pub fn install() -> io::Result<()> {
    if CONFIG.dump_checker_trace {
        let log_dir = &CONFIG.log_dir;
        fs::create_dir_all(log_dir)?;
        let file = fs::File::create(log_dir.join("checker"))?;

        let writer = BoxMakeWriter::new(Arc::new(file));
        let fmt_layer = tracing_subscriber::fmt::layer()
            .with_writer(writer)
            .json()
            .with_filter(Targets::new().with_target("flux_typeck::checker", Level::DEBUG));

        Registry::default().with(fmt_layer).init();
    }

    Ok(())
}
