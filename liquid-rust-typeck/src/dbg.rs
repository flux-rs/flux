#[macro_export]
macro_rules! _run_span {
    ($mode:literal, $tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path($def_id);
        let def_id = path.data.iter().join("::");
        tracing::info_span!($mode, def_id = def_id.as_str())
    }};
}
pub use crate::_run_span as run_span;

#[macro_export]
macro_rules! _basic_block_start {
    ($bb:expr, $pcx:expr, $env:expr) => {{
        tracing::debug!(event = "basic_block_start", bb = ?$bb, pcx = ?$pcx, env = ?$env)
    }};
}
pub use crate::_basic_block_start as basic_block_start;

#[macro_export]
macro_rules! _statement_end {
    ($stmt:expr, $pcx:expr, $env:expr) => {{
        tracing::debug!(event = "statement_end", stmt = ?$stmt, pcx = ?$pcx, env = ?$env)
    }};
}
pub use crate::_statement_end as statement_end;

#[macro_export]
macro_rules! _terminator_end {
    ($terminator:expr, $pcx:expr, $env:expr) => {{
        tracing::debug!(event = "terminator_end", terminator = ?$terminator, pcx = ?$pcx, env = ?$env)
    }};
}
pub use crate::_terminator_end as terminator_end;
