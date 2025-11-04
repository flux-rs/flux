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
use rustc_session::{config, parse::ParseSess};
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
    sopts: &config::Options,
    source_map: Arc<SourceMap>,
    fallback_fluent_bundle: LazyFallbackBundle,
) -> Box<dyn Emitter + sync::DynSend> {
    let translator = Translator { fluent_bundle: None, fallback_fluent_bundle };

    // All the code below is copied from rustc
    let macro_backtrace = sopts.unstable_opts.macro_backtrace;
    let track_diagnostics = sopts.unstable_opts.track_diagnostics;
    let terminal_url = match sopts.unstable_opts.terminal_urls {
        rustc_errors::TerminalUrl::Auto => {
            match (std::env::var("COLORTERM").as_deref(), std::env::var("TERM").as_deref()) {
                (Ok("truecolor"), Ok("xterm-256color"))
                    if sopts.unstable_features.is_nightly_build() =>
                {
                    rustc_errors::TerminalUrl::Yes
                }
                _ => rustc_errors::TerminalUrl::No,
            }
        }
        t => t,
    };

    let source_map = if sopts.unstable_opts.link_only { None } else { Some(source_map) };

    match sopts.error_format {
        config::ErrorOutputType::HumanReadable { kind, color_config } => {
            let short = kind.short();

            if let HumanReadableErrorType::AnnotateSnippet = kind {
                let emitter =
                    AnnotateSnippetEmitter::new(stderr_destination(color_config), translator)
                        .sm(source_map)
                        .short_message(short)
                        .diagnostic_width(sopts.diagnostic_width)
                        .macro_backtrace(macro_backtrace)
                        .track_diagnostics(track_diagnostics)
                        .terminal_url(terminal_url)
                        .theme(if let HumanReadableErrorType::Unicode = kind {
                            rustc_errors::emitter::OutputTheme::Unicode
                        } else {
                            rustc_errors::emitter::OutputTheme::Ascii
                        })
                        .ignored_directories_in_source_blocks(
                            sopts
                                .unstable_opts
                                .ignore_directory_in_diagnostics_source_blocks
                                .clone(),
                        );
                Box::new(emitter.ui_testing(sopts.unstable_opts.ui_testing))
            } else {
                let emitter = HumanEmitter::new(stderr_destination(color_config), translator)
                    .sm(source_map)
                    .short_message(short)
                    .diagnostic_width(sopts.diagnostic_width)
                    .macro_backtrace(macro_backtrace)
                    .track_diagnostics(track_diagnostics)
                    .terminal_url(terminal_url)
                    .theme(if let HumanReadableErrorType::Unicode = kind {
                        rustc_errors::emitter::OutputTheme::Unicode
                    } else {
                        rustc_errors::emitter::OutputTheme::Ascii
                    })
                    .ignored_directories_in_source_blocks(
                        sopts
                            .unstable_opts
                            .ignore_directory_in_diagnostics_source_blocks
                            .clone(),
                    );
                Box::new(emitter.ui_testing(sopts.unstable_opts.ui_testing))
            }
        }
        config::ErrorOutputType::Json { pretty, json_rendered, color_config } => {
            Box::new(
                JsonEmitter::new(
                    Box::new(io::BufWriter::new(io::stderr())),
                    source_map,
                    translator,
                    pretty,
                    json_rendered,
                    color_config,
                )
                .ui_testing(sopts.unstable_opts.ui_testing)
                .ignored_directories_in_source_blocks(
                    sopts
                        .unstable_opts
                        .ignore_directory_in_diagnostics_source_blocks
                        .clone(),
                )
                .diagnostic_width(sopts.diagnostic_width)
                .macro_backtrace(macro_backtrace)
                .track_diagnostics(track_diagnostics)
                .terminal_url(terminal_url),
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
