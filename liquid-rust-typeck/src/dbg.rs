#[macro_export]
macro_rules! _infer_span {
    ($tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path($def_id);
        let def_id = path.data.iter().join("::");
        tracing::info_span!("infer", def_id = def_id.as_str())
    }};
}
pub use crate::_infer_span as infer_span;

#[macro_export]
macro_rules! _check_span {
    ($tcx:expr, $def_id:expr, $bb_envs_infer:expr) => {{
        let path = $tcx.def_path($def_id);
        let def_id = path.data.iter().join("::");
        tracing::info_span!("check", def_id = def_id.as_str(), bb_envs_infer = ?$bb_envs_infer)
    }};
}
pub use crate::_check_span as check_span;

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

#[macro_export]
macro_rules! _check_goto {
    ($target:expr, $pcx:expr, $env:expr, $bb_env:expr) => {{
        tracing::debug!(event = "check_goto", target = ?$target, pcx = ?$pcx, env = ?$env, bb_env = ?$bb_env)
    }};
}
pub use crate::_check_goto as check_goto;

#[macro_export]
macro_rules! _infer_goto_enter {
    ($target:expr, $env:expr, $bb_env:expr) => {{
        if let Some(bb_env) = &$bb_env {
            tracing::debug!(event = "infer_goto_enter", target = ?$target, env = ?&$env, ?bb_env)
        } else {
            tracing::debug!(event = "infer_goto_enter", target = ?$target, env = ?&$env, bb_env = "empty")
        }
    }};
}
pub use crate::_infer_goto_enter as infer_goto_enter;

#[macro_export]
macro_rules! _infer_goto_exit {
    ($target:expr, $bb_env:expr) => {{
        tracing::debug!(event = "infer_goto_exit", target = ?$target, bb_env = ?&$bb_env)
    }};
}
pub use crate::_infer_goto_exit as infer_goto_exit;
