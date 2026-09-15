use flux_errors::E0999;
use flux_macros::InlineDiagnostic as Diagnostic;
use flux_syntax::surface;
use rustc_span::{Span, Symbol};

#[derive(Diagnostic)]
#[diag("integer literal is too large", code = E0999)]
pub(super) struct IntTooLarge {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected literal", code = E0999)]
pub(super) struct UnexpectedLiteral {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid use of path in constructor", code = E0999)]
pub(super) struct InvalidConstructorPath {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag("expected an `&strg` parameter", code = E0999)]
pub(super) struct InvalidLoc {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid suffix `{$suffix}` for number literal", code = E0999)]
pub(super) struct InvalidNumericSuffix {
    #[primary_span]
    #[label(
        "the suffix must be the numeric sort `int`; use a float literal (e.g. `1.0`) for `real`"
    )]
    span: Span,
    suffix: Symbol,
}

impl InvalidNumericSuffix {
    pub(super) fn new(span: Span, suffix: Symbol) -> Self {
        Self { span, suffix }
    }
}

#[derive(Diagnostic)]
#[diag("invalid alias refinement", code = E0999)]
pub(super) struct InvalidAliasReft {
    #[primary_span]
    #[label("this must be a trait")]
    pub(super) span: Span,
}

impl InvalidAliasReft {
    pub(super) fn new(path: &surface::Path) -> Self {
        Self { span: path.span }
    }
}

#[derive(Diagnostic)]
#[diag("invalid variant return type", code = E0999)]
pub(super) struct InvalidVariantRet {
    #[primary_span]
    pub(super) span: Span,
}

impl InvalidVariantRet {
    pub(super) fn new(path: &surface::Path) -> Self {
        Self { span: path.span }
    }
}

#[derive(Diagnostic)]
#[diag("reflected types cannot have refinement annotations", code = E0999)]
pub(super) struct InvalidReflectedVariant {
    #[primary_span]
    pub(super) span: Span,
}

impl InvalidReflectedVariant {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag("multiple spreads found in constructor", code = E0999)]
pub(super) struct MultipleSpreadsInConstructor {
    #[primary_span]
    pub(super) span: Span,
    #[help("previous spread found here. consider removing it")]
    pub(super) prev_span: Span,
}

impl MultipleSpreadsInConstructor {
    pub(super) fn new(span: Span, prev_span: Span) -> Self {
        Self { span, prev_span }
    }
}

#[derive(Diagnostic)]
#[diag("expression not allowed in this position", code = E0999)]
pub(super) struct UnsupportedPosition {
    #[primary_span]
    span: Span,
}

impl UnsupportedPosition {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag("invalid use of `_`", code = E0999)]
pub(super) struct UnsupportedHole {
    #[primary_span]
    #[label("holes cannot be filled in this position")]
    span: Span,
}

impl UnsupportedHole {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag("final associated refinements must have a body", code = E0999)]
pub(super) struct FinalAssocReftWithoutBody {
    #[primary_span]
    span: Span,
}

impl FinalAssocReftWithoutBody {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag("`{$res_descr}` not supported in this position", code = E0999)]
pub(super) struct UnsupportedConstGenericArg {
    #[primary_span]
    #[label("help: try using `_` instead")]
    span: Span,
    res_descr: &'static str,
}

impl UnsupportedConstGenericArg {
    pub(super) fn new(span: Span, res_descr: &'static str) -> Self {
        Self { span, res_descr }
    }
}

#[derive(Diagnostic)]
#[diag("unsupported function signature", code = E0999)]
#[note("{$note}")]
pub(super) struct UnsupportedSignature<'a> {
    #[primary_span]
    pub span: Span,
    pub note: &'a str,
}
