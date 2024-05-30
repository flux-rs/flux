use flux_errors::E0999;
use flux_macros::Diagnostic;
use flux_middle::{fhir, rty};
use rustc_span::{symbol::Ident, Span, Symbol};

#[derive(Diagnostic)]
#[diag(fhir_analysis_sort_mismatch, code = E0999)]
pub(super) struct SortMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: rty::Sort,
    found: rty::Sort,
}

impl SortMismatch {
    pub(super) fn new(span: Span, expected: rty::Sort, found: rty::Sort) -> Self {
        Self { span, expected, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_arg_count_mismatch, code = E0999)]
pub(super) struct ArgCountMismatch {
    #[primary_span]
    #[label]
    span: Option<Span>,
    expected: usize,
    found: usize,
    thing: String,
}

impl ArgCountMismatch {
    pub(super) fn new(span: Option<Span>, thing: String, expected: usize, found: usize) -> Self {
        Self { span, expected, found, thing }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_early_bound_arg_count_mismatch, code = E0999)]
pub(super) struct EarlyBoundArgCountMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: usize,
    found: usize,
}

impl EarlyBoundArgCountMismatch {
    pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
        Self { span, expected, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_duplicated_ensures, code = E0999)]
pub(super) struct DuplicatedEnsures {
    #[primary_span]
    span: Span,
    loc: String,
}

impl DuplicatedEnsures {
    pub(super) fn new(loc: &fhir::PathExpr) -> DuplicatedEnsures {
        Self { span: loc.span, loc: format!("{loc:?}") }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_unknown_qualifier, code = E0999)]
pub(super) struct UnknownQualifier {
    #[primary_span]
    span: Span,
}

impl UnknownQualifier {
    pub(super) fn new(span: Span) -> UnknownQualifier {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_missing_ensures, code = E0999)]
pub(super) struct MissingEnsures {
    #[primary_span]
    span: Span,
}

impl MissingEnsures {
    pub(super) fn new(loc: &fhir::PathExpr) -> MissingEnsures {
        Self { span: loc.span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_expected_fun, code = E0999)]
pub(super) struct ExpectedFun<'a> {
    #[primary_span]
    span: Span,
    found: &'a rty::Sort,
}

impl<'a> ExpectedFun<'a> {
    pub(super) fn new(span: Span, found: &'a rty::Sort) -> Self {
        Self { span, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_invalid_param_in_func_pos, code = E0999)]
pub(super) struct InvalidParamPos<'a> {
    #[primary_span]
    #[label]
    span: Span,
    sort: &'a rty::Sort,
    is_pred: bool,
}

impl<'a> InvalidParamPos<'a> {
    pub(super) fn new(span: Span, sort: &'a rty::Sort) -> Self {
        Self { span, sort, is_pred: sort.is_pred() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_unexpected_fun, code = E0999)]
pub(super) struct UnexpectedFun<'a> {
    #[primary_span]
    #[label]
    span: Span,
    sort: &'a rty::Sort,
}

impl<'a> UnexpectedFun<'a> {
    pub(super) fn new(span: Span, sort: &'a rty::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_param_count_mismatch, code = E0999)]
pub(super) struct ParamCountMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: usize,
    found: usize,
}

impl ParamCountMismatch {
    pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
        Self { span, expected, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_field_not_found, code = E0999)]
pub(super) struct FieldNotFound {
    #[primary_span]
    span: Span,
    sort: rty::Sort,
    fld: Ident,
}

impl FieldNotFound {
    pub(super) fn new(sort: rty::Sort, fld: Ident) -> Self {
        Self { span: fld.span, sort, fld }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_invalid_primitive_dot_access, code = E0999)]
pub(super) struct InvalidPrimitiveDotAccess<'a> {
    #[primary_span]
    span: Span,
    sort: &'a rty::Sort,
}

impl<'a> InvalidPrimitiveDotAccess<'a> {
    pub(super) fn new(sort: &'a rty::Sort, fld: Ident) -> Self {
        Self { sort, span: fld.span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_param_not_determined, code = E0999)]
#[help]
pub(super) struct ParamNotDetermined {
    #[primary_span]
    #[label]
    span: Span,
    name: Symbol,
}

impl ParamNotDetermined {
    pub(super) fn new(span: Span, name: Symbol) -> Self {
        Self { span, name }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_sort_annotation_needed, code = E0999)]
pub(super) struct SortAnnotationNeeded {
    #[primary_span]
    #[label]
    span: Span,
}

impl SortAnnotationNeeded {
    pub(super) fn new(param: &fhir::RefineParam) -> Self {
        Self { span: param.span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_cannot_infer_sort, code = E0999)]
#[note]
pub(super) struct CannotInferSort {
    #[primary_span]
    #[label]
    span: Span,
}

impl CannotInferSort {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_refined_unrefinable_type, code = E0999)]
pub(super) struct RefinedUnrefinableType {
    #[primary_span]
    span: Span,
}

impl RefinedUnrefinableType {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}
