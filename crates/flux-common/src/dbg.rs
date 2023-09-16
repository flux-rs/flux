//! This file contains functions and macros to log debugging information meant for developers.
use std::{
    fmt, fs,
    io::{self, Write},
};

use flux_config as config;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub fn writer_for_item(
    tcx: TyCtxt,
    def_id: DefId,
    ext: impl AsRef<str>,
) -> io::Result<impl io::Write> {
    fs::create_dir_all(config::log_dir())?;
    let path = config::log_dir().join(dump_base_name(tcx, def_id, ext));
    let file = fs::File::create(path)?;
    let buf = std::io::BufWriter::new(file);
    Ok(buf)
}

pub fn dump_item_info<T: fmt::Debug>(
    tcx: TyCtxt,
    def_id: impl Into<DefId>,
    ext: impl AsRef<str>,
    val: &T,
) -> io::Result<()> {
    let mut writer = writer_for_item(tcx, def_id.into(), ext)?;
    write!(writer, "{val:#?}")
}

#[macro_export]
macro_rules! _shape_mode_span {
    ($tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path(rustc_hir::def_id::DefId::from($def_id));
        let def_id = path.data.iter().join("::");
        tracing::info_span!("shape", def_id = def_id.as_str())
    }};
}
pub use crate::_shape_mode_span as shape_mode_span;

#[macro_export]
macro_rules! _refine_mode_span {
    ($tcx:expr, $def_id:expr, $bb_envs:expr) => {{
        let path = $tcx.def_path(rustc_hir::def_id::DefId::from($def_id));
        let def_id = path.data.iter().join("::");
        tracing::info_span!("refine", def_id = def_id.as_str(), bb_envs = ?$bb_envs)
    }};
}
pub use crate::_refine_mode_span as refine_mode_span;

#[macro_export]
macro_rules! _check_fn_span {
    ($tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path(rustc_hir::def_id::DefId::from($def_id));
        let def_id = path.data.iter().join("::");
        tracing::info_span!("check_fn", def_id = def_id.as_str())
    }};
}
pub use crate::_check_fn_span as check_fn_span;

#[macro_export]
macro_rules! _basic_block_start {
    ($bb:expr, $rcx:expr, $env:expr) => {{
        tracing::debug!(event = "basic_block_start", bb = ?$bb, rcx = ?$rcx, env = ?$env)
    }};
}
pub use crate::_basic_block_start as basic_block_start;

#[macro_export]
macro_rules! _statement{
    ($pos:literal, $stmt:expr, $rcx:expr, $env:expr) => {{
        tracing::debug!(event = concat!("statement_", $pos), stmt = ?$stmt, rcx = ?$rcx, env = ?$env)
    }};
}
pub use crate::_statement as statement;

#[macro_export]
macro_rules! _terminator{
    ($pos:literal, $terminator:expr, $rcx:expr, $env:expr) => {{
        tracing::debug!(event = concat!("terminator_", $pos), terminator = ?$terminator, rcx = ?$rcx, env = ?$env)
    }};
}
pub use crate::_terminator as terminator;

#[macro_export]
macro_rules! _refine_goto {
    ($target:expr, $rcx:expr, $env:expr, $bb_env:expr) => {{
        tracing::debug!(event = "refine_goto", target = ?$target, rcx = ?$rcx, env = ?$env, bb_env = ?$bb_env)
    }};
}
pub use crate::_refine_goto as refine_goto;

#[macro_export]
macro_rules! _shape_goto_enter {
    ($target:expr, $env:expr, $bb_env:expr) => {{
        if let Some(bb_env) = &$bb_env {
            tracing::debug!(event = "shape_goto_enter", target = ?$target, env = ?&$env, ?bb_env)
        } else {
            tracing::debug!(event = "shape_goto_enter", target = ?$target, env = ?&$env, bb_env = "empty")
        }
    }};
}
pub use crate::_shape_goto_enter as shape_goto_enter;

#[macro_export]
macro_rules! _shape_goto_exit {
    ($target:expr, $bb_env:expr) => {{
        tracing::debug!(event = "shape_goto_exit", target = ?$target, bb_env = ?&$bb_env)
    }};
}
pub use crate::_shape_goto_exit as shape_goto_exit;

fn dump_base_name(tcx: TyCtxt, def_id: DefId, ext: impl AsRef<str>) -> String {
    let crate_name = tcx.crate_name(def_id.krate);
    let item_name = tcx.def_path(def_id).to_filename_friendly_no_crate();
    format!("{crate_name}.{item_name}.{}", ext.as_ref())
}
