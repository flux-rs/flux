#![feature(rustc_private, never_type)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;

use std::{cell::Cell, sync::Arc};

use flux_common::result::{ErrorCollector, ErrorEmitter};
use rustc_data_structures::sync;
pub use rustc_errors::ErrorGuaranteed;
use rustc_errors::{
    annotate_snippet_emitter_writer::AnnotateSnippetEmitterWriter,
    emitter::{Emitter, EmitterWriter, HumanReadableErrorType},
    json::JsonEmitter,
    registry::Registry,
    DiagnosticId, FatalError, IntoDiagnostic, LazyFallbackBundle,
};
use rustc_session::{
    config::{self, ErrorOutputType},
    parse::ParseSess,
};
use rustc_span::source_map::SourceMap;

pub struct FluxSession {
    pub parse_sess: ParseSess,
}

pub fn diagnostic_id() -> DiagnosticId {
    DiagnosticId::Error("FLUX".to_string())
}

impl FluxSession {
    pub fn new(
        opts: &config::Options,
        source_map: Arc<SourceMap>,
        fallback_bundle: LazyFallbackBundle,
    ) -> Self {
        let emitter = emitter(opts, source_map.clone(), fallback_bundle);
        let handler = rustc_errors::Handler::with_emitter(emitter);
        Self { parse_sess: ParseSess::with_span_handler(handler, source_map) }
    }

    pub fn err_count(&self) -> usize {
        self.parse_sess.span_diagnostic.err_count()
    }

    #[track_caller]
    pub fn emit_err<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        self.parse_sess.emit_err(err)
    }

    #[track_caller]
    pub fn emit_fatal<'a>(&'a self, fatal: impl IntoDiagnostic<'a, !>) -> ! {
        self.parse_sess.emit_fatal(fatal)
    }

    pub fn abort(&self, _: ErrorGuaranteed) -> ! {
        self.parse_sess.span_diagnostic.abort_if_errors();
        FatalError.raise()
    }

    pub fn abort_if_errors(&self) {
        self.parse_sess.span_diagnostic.abort_if_errors();
    }

    pub fn finish_diagnostics(&self) {
        self.parse_sess
            .span_diagnostic
            .print_error_count(&Registry::new(&[]));
        self.abort_if_errors();
    }

    pub fn diagnostic(&self) -> &rustc_errors::Handler {
        &self.parse_sess.span_diagnostic
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
                let emitter = AnnotateSnippetEmitterWriter::new(
                    Some(source_map),
                    None,
                    fallback_bundle,
                    short,
                    false,
                );
                Box::new(emitter)
            } else {
                let emitter = EmitterWriter::stderr(color_config, fallback_bundle)
                    .sm(Some(source_map))
                    .short_message(short)
                    .track_diagnostics(track_diagnostics)
                    .terminal_url(opts.unstable_opts.terminal_urls);
                Box::new(emitter)
            }
        }
        ErrorOutputType::Json { pretty, json_rendered } => {
            Box::new(JsonEmitter::stderr(
                Some(Registry::new(&[])),
                source_map,
                bundle,
                fallback_bundle,
                pretty,
                json_rendered,
                None,
                false,
                track_diagnostics,
                opts.unstable_opts.terminal_urls,
            ))
        }
    }
}

impl ErrorEmitter for FluxSession {
    fn emit<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
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
    pub fn emit<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
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
    fn emit<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
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
