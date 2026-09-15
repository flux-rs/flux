use flux_errors::E0999;
use flux_macros::Diagnostic;
use flux_middle::{fhir, rty};
use rustc_span::{Span, Symbol, symbol::Ident};

#[derive(Diagnostic)]
#[diag("mismatched sorts", code = E0999)]
pub(super) struct SortMismatch {
    #[primary_span]
    #[label("expected `{$expected}`, found `{$found}`")]
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
#[diag("this {$thing} takes {$expected ->
        [one] {$expected} refinement argument
        *[other] {$expected} refinement arguments
    } but {$found ->
        [one] {$found} was found
        *[other] {$found} were found
    }", code = E0999)]
pub(super) struct ArgCountMismatch {
    #[primary_span]
    #[label(
        "expected {$expected ->
            [one] {$expected} argument
            *[other] {$expected} arguments
        }, found {$found}"
    )]
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
#[diag("an ensures clause already exists for `{$loc}`", code = E0999)]
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
#[diag("missing ensures clause for `&strg` reference", code = E0999)]
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
#[diag("properties for `{$op}` are not yet supported", code = E0999)]
pub(super) struct UnsupportedPrimOp {
    #[primary_span]
    span: Span,
    op: fhir::BinOp,
}

impl UnsupportedPrimOp {
    pub(super) fn new(span: Span, op: fhir::BinOp) -> Self {
        Self { span, op }
    }
}

#[derive(Diagnostic)]
#[diag("wildcard parameter cannot have sort `{$found}`", code = E0999)]
#[note(
    "a wildcard parameter is instantiated with literal constants, so its sort must be one that has literals: `int`, `real`, `str`, or a bit vector"
)]
pub(super) struct InvalidWildcardSort {
    #[primary_span]
    #[label("this parameter is marked as a wildcard with `#`")]
    span: Span,
    found: rty::Sort,
}

impl InvalidWildcardSort {
    pub(super) fn new(span: Span, found: rty::Sort) -> Self {
        Self { span, found }
    }
}

#[derive(Diagnostic)]
#[diag("expected function, found `{$found}`", code = E0999)]
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
#[diag("illegal use of refinement parameter", code = E0999)]
pub(super) struct InvalidParamPos<'a> {
    #[primary_span]
    #[label(
        "{$is_pred ->
            [true] abstract refinements are only allowed in a top-level conjunction
            *[false] parameters of sort `{$sort}` are not supported in this position
        }"
    )]
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
#[diag("mismatched sorts", code = E0999)]
pub(super) struct UnexpectedFun<'a> {
    #[primary_span]
    #[label("expected `{$sort}`, found function")]
    span: Span,
    sort: &'a rty::Sort,
}

impl<'a> UnexpectedFun<'a> {
    pub(super) fn new(span: Span, sort: &'a rty::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag("mismatched sorts", code = E0999)]
pub(super) struct UnexpectedConstructor<'a> {
    #[primary_span]
    #[label("expected `{$sort}`, found constructor")]
    span: Span,
    sort: &'a rty::Sort,
}

impl<'a> UnexpectedConstructor<'a> {
    pub(super) fn new(span: Span, sort: &'a rty::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag("parameter count mismatch", code = E0999)]
pub(super) struct ParamCountMismatch {
    #[primary_span]
    #[label(
        "this function has {$found ->
            [one] {$found} parameter
            *[other] {$found} parameters
        }, but a function with {$expected ->
            [one] {$expected} parameter
            *[other] {$expected} parameters
        } was expected"
    )]
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
#[diag("no field `{$fld}` on sort `{$sort}`", code = E0999)]
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
#[diag("missing fields in constructor: {$missing_fields}", code = E0999)]
pub(super) struct ConstructorMissingFields {
    #[primary_span]
    constructor_span: Span,
    missing_fields: String,
}

impl ConstructorMissingFields {
    pub(super) fn new(constructor_span: Span, missing_fields: Vec<Symbol>) -> Self {
        let missing_fields = missing_fields
            .into_iter()
            .map(|x| format!("`{x}`"))
            .collect::<Vec<String>>()
            .join(", ");
        Self { constructor_span, missing_fields }
    }
}

#[derive(Diagnostic)]
#[diag("field `{$fld}` was previously used in constructor", code = E0999)]
pub(super) struct DuplicateFieldUsed {
    #[primary_span]
    span: Span,
    fld: Ident,
    #[help("field `{$fld}` previously used here, consider removing it")]
    previous_span: Span,
}

impl DuplicateFieldUsed {
    pub(super) fn new(fld: Ident, previous_fld: Ident) -> Self {
        Self { span: fld.span, fld, previous_span: previous_fld.span }
    }
}

#[derive(Diagnostic)]
#[diag("`{$sort}` is a primitive sort and therefore doesn't have fields", code = E0999)]
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
#[diag("parameter `{$name}` cannot be determined", code = E0999)]
#[help("try indexing a type with `{$name}` in a position that fully determines its value")]
pub(super) struct ParamNotDetermined {
    #[primary_span]
    #[label("undetermined parameter")]
    span: Span,
    name: Symbol,
}

impl ParamNotDetermined {
    pub(super) fn new(span: Span, name: Symbol) -> Self {
        Self { span, name }
    }
}

#[derive(Diagnostic)]
#[diag("sort annotation needed", code = E0999)]
pub(super) struct SortAnnotationNeeded {
    #[primary_span]
    #[label("help: consider giving this parameter an explicit sort")]
    span: Span,
}

impl SortAnnotationNeeded {
    pub(super) fn new(param: &fhir::RefineParam) -> Self {
        Self { span: param.span }
    }
}

#[derive(Diagnostic)]
#[diag("bounded quantification requires `int`-sorted binders", code = E0999)]
#[note("binder inferred to have incompatible sort `{$sort}`")]
pub(super) struct IllSortedQuantifier {
    #[primary_span]
    #[label("invalid sort")]
    span: Span,
    sort: rty::Sort,
}

impl IllSortedQuantifier {
    pub(super) fn new(span: Span, sort: rty::Sort) -> Self {
        Self { span, sort }
    }
}

#[derive(Diagnostic)]
#[diag("sort annotation needed", code = E0999)]
#[note("sort must be known at this point")]
pub(super) struct CannotInferSort {
    #[primary_span]
    #[label("cannot infer sort")]
    span: Span,
}

impl CannotInferSort {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }
}

#[derive(Diagnostic)]
#[diag("invalid cast from `{$from}` to `{$to}`", code = E0999)]
#[note("use `allow_uninterpreted_cast` to enable this cast")]
pub(super) struct InvalidCast {
    #[primary_span]
    #[label("invalid cast")]
    span: Span,
    from: String,
    to: String,
}

impl InvalidCast {
    pub(super) fn new(span: Span, from: &rty::Sort, to: &rty::Sort) -> Self {
        Self { span, from: format!("{from:?}"), to: format!("{to:?}") }
    }
}
