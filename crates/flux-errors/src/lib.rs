#![feature(rustc_private, never_type)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;

use std::{cell::Cell, io, sync::Arc};

use flux_common::result::{ErrorCollector, ErrorEmitter};
use rustc_data_structures::sync;
pub use rustc_errors::ErrorGuaranteed;
use rustc_errors::{
    Diagnostic, ErrCode, FatalAbort, FatalError, LazyFallbackBundle,
    annotate_snippet_emitter_writer::AnnotateSnippetEmitter,
    emitter::{Emitter, HumanEmitter, HumanReadableErrorType, stderr_destination},
    json::JsonEmitter,
    translation::Translator,
};
use rustc_session::{
    config::{self, ErrorOutputType},
    parse::ParseSess,
};
use rustc_span::source_map::SourceMap;

pub struct FluxSession {
    pub parse_sess: ParseSess,
}

// FIXME(nilehmann) We probably need to move out of this error reporting
pub const E0999: ErrCode = ErrCode::from_u32(999);

impl FluxSession {
    pub fn new(
        opts: &config::Options,
        source_map: Arc<SourceMap>,
        fallback_bundle: LazyFallbackBundle,
    ) -> Self {
        let emitter = emitter(opts, source_map.clone(), fallback_bundle);
        let dcx = rustc_errors::DiagCtxt::new(emitter);
        Self { parse_sess: ParseSess::with_dcx(dcx, source_map) }
    }

    pub fn err_count(&self) -> usize {
        self.parse_sess.dcx().err_count()
    }

    #[track_caller]
    pub fn emit_err<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        self.parse_sess.dcx().emit_err(err)
    }

    #[track_caller]
    pub fn emit_fatal<'a>(&'a self, fatal: impl Diagnostic<'a, FatalAbort>) -> ! {
        self.parse_sess.dcx().emit_fatal(fatal)
    }

    pub fn abort(&self, _: ErrorGuaranteed) -> ! {
        self.parse_sess.dcx().abort_if_errors();
        FatalError.raise()
    }

    pub fn abort_if_errors(&self) {
        self.parse_sess.dcx().abort_if_errors();
    }

    pub fn finish_diagnostics(&self) {
        self.parse_sess.dcx().print_error_count();
        self.abort_if_errors();
    }

    pub fn dcx(&self) -> &rustc_errors::DiagCtxt {
        &self.parse_sess.dcx()
    }
}

fn emitter(
    opts: &config::Options,
    source_map: Arc<SourceMap>,
    fallback_fluent_bundle: LazyFallbackBundle,
) -> Box<dyn Emitter + sync::DynSend> {
    let track_diagnostics = opts.unstable_opts.track_diagnostics;

    let translator = Translator { fluent_bundle: None, fallback_fluent_bundle };
    match opts.error_format {
        ErrorOutputType::HumanReadable { kind, color_config } => {
            if let HumanReadableErrorType::AnnotateSnippet = kind {
                let emitter =
                    AnnotateSnippetEmitter::new(Some(source_map), translator, false, false);
                Box::new(emitter)
            } else {
                let dst = stderr_destination(color_config);
                let emitter = HumanEmitter::new(dst, translator)
                    .sm(Some(source_map))
                    .short_message(kind.short())
                    .diagnostic_width(opts.diagnostic_width)
                    .track_diagnostics(track_diagnostics)
                    .terminal_url(opts.unstable_opts.terminal_urls);
                Box::new(emitter)
            }
        }
        ErrorOutputType::Json { pretty, json_rendered, color_config } => {
            Box::new(
                JsonEmitter::new(
                    Box::new(io::BufWriter::new(io::stderr())),
                    Some(source_map),
                    translator,
                    pretty,
                    json_rendered,
                    color_config,
                )
                .track_diagnostics(track_diagnostics)
                .diagnostic_width(opts.diagnostic_width)
                .terminal_url(opts.unstable_opts.terminal_urls),
            )
        }
    }
}

impl ErrorEmitter for FluxSession {
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        self.emit_err(err)
    }
}

/// Convenience struct implementing [`ErrorEmitter`] and [`ErrorCollector`]
pub struct Errors<'sess> {
    sess: &'sess FluxSession,
    err: Cell<Option<ErrorGuaranteed>>,
}

impl<'sess> Errors<'sess> {
    pub fn new(sess: &'sess FluxSession) -> Self {
        Self { sess, err: Cell::new(None) }
    }

    pub fn has_errors(&self) -> bool {
        self.err.get().is_some()
    }

    #[track_caller]
    pub fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        let err = self.sess.emit_err(err);
        self.err.set(Some(err));
        err
    }

    pub fn to_result(&self) -> Result<(), ErrorGuaranteed> {
        if let Some(err) = self.err.get() { Err(err) } else { Ok(()) }
    }
}

impl ErrorEmitter for Errors<'_> {
    #[track_caller]
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        Errors::emit(self, err)
    }
}

impl ErrorCollector<ErrorGuaranteed> for Errors<'_> {
    type Result = Result<(), ErrorGuaranteed>;

    fn collect(&mut self, err: ErrorGuaranteed) {
        *self.err.get_mut() = Some(err);
    }

    fn into_result(self) -> Self::Result {
        Errors::to_result(&self)
    }
}
