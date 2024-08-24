use flux_errors::E0999;
use flux_macros::Diagnostic;
use flux_syntax::surface;
use rustc_span::{symbol::Ident, Span, Symbol};

#[derive(Diagnostic)]
#[diag(desugar_int_too_large, code = E0999)]
pub(super) struct IntTooLarge {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_unexpected_literal, code = E0999)]
pub(super) struct UnexpectedLiteral {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_dot_var, code = E0999)]
pub(super) struct InvalidDotVar {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_func_as_var, code = E0999)]
pub(super) struct InvalidFuncAsVar {
    #[primary_span]
    #[label]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_func, code = E0999)]
pub(super) struct InvalidFunc {
    #[primary_span]
    #[label]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_loc, code = E0999)]
pub(super) struct InvalidLoc {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_numeric_suffix, code = E0999)]
pub(super) struct InvalidNumericSuffix {
    #[primary_span]
    #[label]
    span: Span,
    suffix: Symbol,
}

impl InvalidNumericSuffix {
    pub(super) fn new(span: Span, suffix: Symbol) -> Self {
        Self { span, suffix }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_unresolved_generic_param, code = E0999)]
#[note]
pub(super) struct UnresolvedGenericParam {
    #[primary_span]
    span: Span,
}

impl UnresolvedGenericParam {
    pub(super) fn new(param: Ident) -> Self {
        Self { span: param.span }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_alias_reft, code = E0999)]
pub(super) struct InvalidAliasReft {
    #[primary_span]
    #[label]
    pub(super) span: Span,
}

impl InvalidAliasReft {
    pub(super) fn new(path: &surface::Path) -> Self {
        Self { span: path.span }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_variant_ret, code = E0999)]
pub(super) struct InvalidVariantRet {
    #[primary_span]
    pub(super) span: Span,
}

impl InvalidVariantRet {
    pub(super) fn new(path: &surface::Path) -> Self {
        Self { span: path.span }
    }
}
