//! This file contains functions and macros to log debugging information meant for developers.
use std::{
    fmt, fs,
    io::{self, Write},
};

use flux_config as config;
use flux_macros::DebugAsJson;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use serde::Serialize;

#[derive(Serialize, DebugAsJson)]
pub struct SpanTrace {
    file: Option<String>,
    start_line: usize,
    start_col: usize,
    end_line: usize,
    end_col: usize,
}

impl SpanTrace {
    fn span_file(tcx: TyCtxt, span: Span) -> Option<String> {
        let sm = tcx.sess.source_map();
        let current_dir = &tcx.sess.opts.working_dir;
        let current_dir = current_dir.local_path()?;
        if let rustc_span::FileName::Real(file_name) = sm.span_to_filename(span) {
            let file_path = file_name.local_path()?;
            let full_path = current_dir.join(file_path);
            Some(full_path.display().to_string())
        } else {
            None
        }
    }
    pub fn new(tcx: TyCtxt, span: Span) -> Self {
        let sm = tcx.sess.source_map();
        let (_, start_line, start_col, end_line, end_col) = sm.span_to_location_info(span);
        let file = SpanTrace::span_file(tcx, span);
        SpanTrace { file, start_line, start_col, end_line, end_col }
    }
}

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
    val: T,
) -> io::Result<()> {
    let mut writer = writer_for_item(tcx, def_id.into(), ext)?;
    writeln!(writer, "{val:#?}")
}

#[macro_export]
macro_rules! _shape_mode_span {
    ($tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path_str(rustc_hir::def_id::DefId::from($def_id));
        tracing::info_span!("shape", def_id = path.as_str())
    }};
}
pub use crate::_shape_mode_span as shape_mode_span;

#[macro_export]
macro_rules! _refine_mode_span {
    ($tcx:expr, $def_id:expr, $bb_envs:expr) => {{
        let path = $tcx.def_path_str(rustc_hir::def_id::DefId::from($def_id));
        tracing::info_span!("refine", def_id = path.as_str(), bb_envs = ?$bb_envs)
    }};
}
pub use crate::_refine_mode_span as refine_mode_span;

#[macro_export]
macro_rules! _check_fn_span {
    ($tcx:expr, $def_id:expr) => {{
        let path = $tcx.def_path_str(rustc_hir::def_id::DefId::from($def_id));
        tracing::info_span!("check_fn", def_id = path.as_str())
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
macro_rules! _solution {
    ($genv:expr, $sol:expr, $span:expr) => {{
        if config::dump_checker_trace_info() {
          let genv = $genv;
          let sol_json = SolutionTrace::new(genv, $sol);
          let span_json = SpanTrace::new(genv.tcx(), $span);
          tracing::info!(event = "solution", span = ?$span, solution = ?sol_json)
        }
    }};
}
pub use crate::_solution as solution;

#[macro_export]
macro_rules! _statement{
    ($pos:literal, $stmt:expr, $infcx:expr, $env:expr, $span:expr, $checker:expr) => {{
        if config::dump_checker_trace_info() {
          let rcx = $infcx.cursor();
          let ck = $checker;
          let genv = ck.genv;
          let local_names = &ck.body.local_names;
          let local_decls = &ck.body.local_decls;
          let rcx_json = RefineCtxtTrace::new(genv, rcx);
          let env_json = TypeEnvTrace::new(genv, local_names, local_decls, $env);
          let span_json = SpanTrace::new(genv.tcx(), $span);
          tracing::info!(event = concat!("statement_", $pos), stmt = ?$stmt, stmt_span = ?$span, rcx = ?rcx, env = ?$env, rcx_json = ?rcx_json, env_json = ?env_json, stmt_span_json = ?span_json)
        }
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

#[macro_export]
macro_rules! _hyperlink {
    ($tcx:expr, $src_span:expr, $dst_span:expr) => {{
       let src_json = SpanTrace::new($tcx, $src_span);
       let dst_json = SpanTrace::new($tcx, $dst_span);
       tracing::warn!(event = "hyperlink", src_span = ?src_json, dst_span = ?dst_json)
    }};
}
pub use crate::_hyperlink as hyperlink;

fn dump_base_name(tcx: TyCtxt, def_id: DefId, ext: impl AsRef<str>) -> String {
    let crate_name = tcx.crate_name(def_id.krate);
    let item_name = tcx.def_path(def_id).to_filename_friendly_no_crate();
    format!("{crate_name}.{item_name}.{}", ext.as_ref())
}

#[macro_export]
macro_rules! _debug_assert_eq3 {
    ($e1:expr, $e2:expr, $e3:expr) => {{
        debug_assert!($e1 == $e2 && $e2 == $e3, "{:?} != {:?} != {:?}", $e1, $e2, $e3);
    }};
}
pub use crate::_debug_assert_eq3 as debug_assert_eq3;
