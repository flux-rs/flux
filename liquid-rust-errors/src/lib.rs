#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_macros;
extern crate rustc_session;
extern crate rustc_span;

use std::rc::Rc;

use rustc_data_structures::sync;
use rustc_errors::{
    annotate_snippet_emitter_writer::AnnotateSnippetEmitterWriter,
    emitter::{Emitter, EmitterWriter, HumanReadableErrorType},
    json::JsonEmitter,
    registry::Registry,
    DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage,
};
use rustc_macros::fluent_messages;
use rustc_session::{config::ErrorOutputType, parse::ParseSess, SessionDiagnostic};
use rustc_span::source_map::SourceMap;

fluent_messages! {
    refineck => "../locales/en-US/refineck.ftl",
}

pub use fluent_generated::{self as fluent, DEFAULT_LOCALE_RESOURCES};

pub struct LiquidRustSession {
    pub parse_sess: ParseSess,
}

impl LiquidRustSession {
    pub fn new(error_format: ErrorOutputType, source_map: Rc<SourceMap>) -> Self {
        let emitter = emitter(error_format, source_map.clone());
        let handler = rustc_errors::Handler::with_emitter(true, None, emitter);
        Self { parse_sess: ParseSess::with_span_handler(handler, source_map) }
    }

    pub fn emit_err<'a>(&'a self, err: impl SessionDiagnostic<'a>) -> ErrorGuaranteed {
        err.into_diagnostic(&self.parse_sess).emit()
    }

    pub fn abort_if_errors(&self) {
        self.parse_sess.span_diagnostic.abort_if_errors()
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
