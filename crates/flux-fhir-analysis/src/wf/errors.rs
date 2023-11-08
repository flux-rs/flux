use flux_macros::Diagnostic;
use flux_middle::fhir::{self, SurfaceIdent};
use rustc_span::{Span, Symbol};

#[derive(Diagnostic)]
#[diag(fhir_analysis_sort_mismatch, code = "FLUX")]
pub(super) struct SortMismatch {
    #[primary_span]
    #[label]
    span: Span,
    expected: fhir::Sort,
    found: fhir::Sort,
}

impl SortMismatch {
    pub(super) fn new(span: Span, expected: fhir::Sort, found: fhir::Sort) -> Self {
        Self { span, expected, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_arg_count_mismatch, code = "FLUX")]
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
#[diag(fhir_analysis_early_bound_arg_count_mismatch, code = "FLUX")]
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
#[diag(fhir_analysis_duplicated_ensures, code = "FLUX")]
pub(super) struct DuplicatedEnsures {
    #[primary_span]
    span: Span,
    loc: Symbol,
}

impl DuplicatedEnsures {
    pub(super) fn new(loc: &fhir::Ident) -> DuplicatedEnsures {
        Self { span: loc.span(), loc: loc.sym() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_unknown_qualifier, code = "FLUX")]
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
#[diag(fhir_analysis_missing_ensures, code = "FLUX")]
pub(super) struct MissingEnsures {
    #[primary_span]
    span: Span,
}

impl MissingEnsures {
    pub(super) fn new(loc: &fhir::Ident) -> MissingEnsures {
        Self { span: loc.span() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_expected_fun, code = "FLUX")]
pub(super) struct ExpectedFun<'a> {
    #[primary_span]
    span: Span,
    found: &'a fhir::Sort,
}

impl<'a> ExpectedFun<'a> {
    pub(super) fn new(span: Span, found: &'a fhir::Sort) -> Self {
        Self { span, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_invalid_param_in_func_pos, code = "FLUX")]
pub(super) struct InvalidParamPos<'a> {
    #[primary_span]
    #[label]
    span: Span,
    sort: &'a fhir::Sort,
    is_pred: bool,
}

impl<'a> InvalidParamPos<'a> {
    pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
        Self { span, sort, is_pred: sort.is_pred() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_unexpected_fun, code = "FLUX")]
pub(super) struct UnexpectedFun<'a> {
    #[primary_span]
    #[label]
    span: Span,
    sort: &'a fhir::Sort,
}

impl<'a> UnexpectedFun<'a> {
    pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_expected_numeric, code = "FLUX")]
pub(super) struct ExpectedNumeric<'a> {
    #[primary_span]
    #[label]
    span: Span,
    found: &'a fhir::Sort,
}

impl<'a> ExpectedNumeric<'a> {
    pub(super) fn new(span: Span, found: &'a fhir::Sort) -> Self {
        Self { span, found }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_param_count_mismatch, code = "FLUX")]
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
#[diag(fhir_analysis_field_not_found, code = "FLUX")]
pub(super) struct FieldNotFound {
    #[primary_span]
    span: Span,
    sort: fhir::Sort,
    fld: SurfaceIdent,
}

impl FieldNotFound {
    pub(super) fn new(sort: fhir::Sort, fld: SurfaceIdent) -> Self {
        Self { span: fld.span, sort, fld }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_invalid_primitive_dot_access, code = "FLUX")]
pub(super) struct InvalidPrimitiveDotAccess<'a> {
    #[primary_span]
    span: Span,
    sort: &'a fhir::Sort,
}

impl<'a> InvalidPrimitiveDotAccess<'a> {
    pub(super) fn new(sort: &'a fhir::Sort, fld: SurfaceIdent) -> Self {
        Self { sort, span: fld.span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_invalid_base_instance, code = "FLUX")]
pub(super) struct InvalidBaseInstance<'a> {
    #[primary_span]
    span: Span,
    ty: &'a fhir::Ty,
}

impl<'a> InvalidBaseInstance<'a> {
    pub(super) fn new(ty: &'a fhir::Ty) -> Self {
        Self { ty, span: ty.span }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_no_equality, code = "FLUX")]
pub(super) struct NoEquality<'a> {
    #[primary_span]
    span: Span,
    sort: &'a fhir::Sort,
}

impl<'a> NoEquality<'a> {
    pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_param_not_determined, code = "FLUX")]
#[help]
pub(super) struct ParamNotDetermined {
    #[primary_span]
    #[label]
    span: Span,
    sym: Symbol,
}

impl ParamNotDetermined {
    pub(super) fn new(ident: fhir::Ident) -> Self {
        Self { span: ident.span(), sym: ident.sym() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_sort_annotation_needed, code = "FLUX")]
pub(super) struct SortAnnotationNeeded {
    #[primary_span]
    #[label]
    span: Span,
}

impl SortAnnotationNeeded {
    pub(super) fn new(param: &fhir::RefineParam) -> Self {
        Self { span: param.ident.span() }
    }
}

#[derive(Diagnostic)]
#[diag(fhir_analysis_cannot_infer_sort, code = "FLUX")]
#[note]
pub(super) struct CannotInferSort {
    #[primary_span]
    #[label]
    span: Span,
}

impl CannotInferSort {
    pub(super) fn new(ident: fhir::Ident) -> Self {
        Self { span: ident.span() }
    }
}
