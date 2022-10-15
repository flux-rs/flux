#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;

use std::rc::Rc;

use flux_macros::fluent_messages;
use rustc_data_structures::sync;
pub use rustc_errors::ErrorGuaranteed;
use rustc_errors::{
    annotate_snippet_emitter_writer::AnnotateSnippetEmitterWriter,
    emitter::{Emitter, EmitterWriter, HumanReadableErrorType},
    json::JsonEmitter,
    registry::Registry,
    DiagnosticMessage, IntoDiagnostic, SubdiagnosticMessage,
};
use rustc_session::{config::ErrorOutputType, parse::ParseSess};
use rustc_span::source_map::SourceMap;

fluent_messages! {
    parse => "../locales/en-US/parse.ftl",
    resolver => "../locales/en-US/resolver.ftl",
    desugar => "../locales/en-US/desugar.ftl",
    wf => "../locales/en-US/wf.ftl",
    refineck => "../locales/en-US/refineck.ftl",
    invariants => "../locales/en-US/invariants.ftl",
}

pub use fluent_generated::{self as fluent, DEFAULT_LOCALE_RESOURCES};

pub struct FluxSession {
    pub parse_sess: ParseSess,
}

impl FluxSession {
    pub fn new(error_format: ErrorOutputType, source_map: Rc<SourceMap>) -> Self {
        let emitter = emitter(error_format, source_map.clone());
        let handler = rustc_errors::Handler::with_emitter(true, None, emitter);
        Self { parse_sess: ParseSess::with_span_handler(handler, source_map) }
    }

    pub fn emit_err<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        err.into_diagnostic(&self.parse_sess.span_diagnostic).emit()
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
}

fn emitter(
    error_format: ErrorOutputType,
    source_map: Rc<SourceMap>,
) -> Box<dyn Emitter + sync::Send> {
    let fallback_bundle = rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES, false);
    let bundle = None;

    match error_format {
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
                let emitter = EmitterWriter::stderr(
                    color_config,
                    Some(source_map),
                    bundle,
                    fallback_bundle,
                    short,
                    false,
                    None,
                    false,
                );
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
            ))
        }
    }
}

pub trait ResultExt<T, E> {
    fn emit<'a>(self, sess: &'a FluxSession) -> Result<T, ErrorGuaranteed>
    where
        E: IntoDiagnostic<'a>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn emit<'a>(self, sess: &'a FluxSession) -> Result<T, ErrorGuaranteed>
    where
        E: IntoDiagnostic<'a>,
    {
        match self {
            Ok(v) => Ok(v),
            Err(err) => Err(sess.emit_err(err)),
        }
    }
}
