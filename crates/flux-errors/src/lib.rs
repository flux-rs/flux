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
    annotate_snippet_emitter_writer::AnnotateSnippetEmitter,
    emitter::{stderr_destination, Emitter, HumanEmitter, HumanReadableErrorType},
    json::JsonEmitter,
    registry::Registry,
    Diagnostic, ErrCode, FatalAbort, FatalError, LazyFallbackBundle,
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
        self.parse_sess.dcx.err_count()
    }

    #[track_caller]
    pub fn emit_err<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        self.parse_sess.dcx.emit_err(err)
    }

    #[track_caller]
    pub fn emit_fatal<'a>(&'a self, fatal: impl Diagnostic<'a, FatalAbort>) -> ! {
        self.parse_sess.dcx.emit_fatal(fatal)
    }

    pub fn abort(&self, _: ErrorGuaranteed) -> ! {
        self.parse_sess.dcx.abort_if_errors();
        FatalError.raise()
    }

    pub fn abort_if_errors(&self) {
        self.parse_sess.dcx.abort_if_errors();
    }

    pub fn finish_diagnostics(&self) {
        self.parse_sess.dcx.print_error_count(&Registry::new(&[]));
        self.abort_if_errors();
    }

    pub fn dcx(&self) -> &rustc_errors::DiagCtxt {
        &self.parse_sess.dcx
    }
}

fn emitter(
    opts: &config::Options,
    source_map: Arc<SourceMap>,
    fallback_bundle: LazyFallbackBundle,
) -> Box<dyn Emitter + sync::DynSend> {
    let bundle = None;
    let track_diagnostics = opts.unstable_opts.track_diagnostics;

    match opts.error_format {
        ErrorOutputType::HumanReadable(kind) => {
            let (short, color_config) = kind.unzip();
            if let HumanReadableErrorType::AnnotateSnippet(_) = kind {
                let emitter = AnnotateSnippetEmitter::new(
                    Some(source_map),
                    None,
                    fallback_bundle,
                    short,
                    false,
                );
                Box::new(emitter)
            } else {
                let dst = stderr_destination(color_config);
                let emitter = HumanEmitter::new(dst, fallback_bundle)
                    .sm(Some(source_map))
                    .short_message(short)
                    .track_diagnostics(track_diagnostics)
                    .terminal_url(opts.unstable_opts.terminal_urls);
                Box::new(emitter)
            }
        }
        ErrorOutputType::Json { pretty, json_rendered } => {
            Box::new(
                JsonEmitter::new(
                    Box::new(io::BufWriter::new(io::stderr())),
                    source_map,
                    fallback_bundle,
                    pretty,
                    json_rendered,
                )
                .fluent_bundle(bundle)
                .track_diagnostics(track_diagnostics)
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

/// Convience struct implementing [`ErrorEmitter`] and [`ErrorCollector`]
pub struct Errors<'sess> {
    sess: &'sess FluxSession,
    err: Cell<Option<ErrorGuaranteed>>,
}

impl<'sess> Errors<'sess> {
    pub fn new(sess: &'sess FluxSession) -> Self {
        Self { sess, err: Cell::new(None) }
    }

    #[track_caller]
    pub fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        let err = self.sess.emit_err(err);
        self.err.set(Some(err));
        err
    }

    pub fn into_result(self) -> Result<(), ErrorGuaranteed> {
        if let Some(err) = self.err.into_inner() {
            Err(err)
        } else {
            Ok(())
        }
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

    fn collect_err(&mut self, err: ErrorGuaranteed) {
        *self.err.get_mut() = Some(err);
    }

    fn into_result(self) -> Self::Result {
        Errors::into_result(self)
    }
}
