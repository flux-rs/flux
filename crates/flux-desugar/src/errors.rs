use flux_macros::Diagnostic;
use flux_syntax::surface::{self, BindKind, QPathExpr};
use itertools::Itertools;
use rustc_span::{symbol::Ident, Span, Symbol};

#[derive(Diagnostic)]
#[diag(desugar_unresolved_var, code = "FLUX")]
pub(super) struct UnresolvedVar {
    #[primary_span]
    #[label]
    span: Span,
    var: String,
}

impl UnresolvedVar {
    pub(super) fn from_qpath(qpath: &QPathExpr) -> Self {
        Self {
            span: qpath.span,
            var: format!("{}", qpath.segments.iter().format_with("::", |s, f| f(&s.name))),
        }
    }

    pub(super) fn from_ident(ident: Ident) -> Self {
        Self { span: ident.span, var: format!("{ident}") }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_duplicate_param, code = "FLUX")]
pub(super) struct DuplicateParam {
    #[primary_span]
    #[label]
    span: Span,
    name: Symbol,
    #[label(desugar_first_use)]
    first_use: Span,
}

impl DuplicateParam {
    pub(super) fn new(old_ident: Ident, new_ident: Ident) -> Self {
        debug_assert_eq!(old_ident.name, new_ident.name);
        Self { span: new_ident.span, name: new_ident.name, first_use: old_ident.span }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_unresolved_sort, code = "FLUX")]
pub(super) struct UnresolvedSort {
    #[primary_span]
    #[label]
    span: Span,
    sort: Ident,
}

impl UnresolvedSort {
    pub(super) fn new(sort: Ident) -> Self {
        Self { span: sort.span, sort }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_int_too_large, code = "FLUX")]
pub(super) struct IntTooLarge {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_unexpected_literal, code = "FLUX")]
pub(super) struct UnexpectedLiteral {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_dot_var, code = "FLUX")]
pub(super) struct InvalidDotVar {
    #[primary_span]
    pub(super) span: Span,
}

#[derive(Diagnostic)]
#[diag(desugar_sort_arity_mismatch, code = "FLUX")]
pub(super) struct SortArityMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: usize,
    found: usize,
}

impl SortArityMismatch {
    pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
        Self { span, expected, found }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_refine_arg_count_mismatch, code = "FLUX")]
pub(super) struct RefineArgCountMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: usize,
    found: usize,
}

impl RefineArgCountMismatch {
    pub(super) fn new(idxs: &surface::Indices, expected: usize) -> Self {
        Self { span: idxs.span, expected, found: idxs.indices.len() }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_unrefined_param, code = "FLUX")]
pub(super) struct InvalidUnrefinedParam {
    #[primary_span]
    #[label]
    span: Span,
    var: Ident,
}

impl InvalidUnrefinedParam {
    pub(super) fn new(var: Ident) -> Self {
        Self { var, span: var.span }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_invalid_numeric_suffix, code = "FLUX")]
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
#[diag(desugar_refined_unrefinable_type, code = "FLUX")]
pub(super) struct RefinedUnrefinableType {
    #[primary_span]
    span: Span,
}

impl RefinedUnrefinableType {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag(desugar_unresolved_generic_param, code = "FLUX")]
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
#[diag(desugar_illegal_binder, code = "FLUX")]
pub(super) struct IllegalBinder {
    #[primary_span]
    #[label]
    span: Span,
    kind: &'static str,
}

impl IllegalBinder {
    pub(super) fn new(span: Span, kind: BindKind) -> Self {
        Self { span, kind: kind.token_str() }
    }
}
