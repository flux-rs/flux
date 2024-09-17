#![feature(proc_macro_diagnostic, never_type, proc_macro_span, let_chains, if_let_guard)]

mod diagnostics;
mod fold;
mod primops;

use synstructure::decl_derive;

decl_derive!(
    [Diagnostic, attributes(
        // struct attributes
        diag,
        help,
        note,
        warning,
        // field attributes
        skip_arg,
        primary_span,
        label,
        subdiagnostic,
        suggestion,
        suggestion_short,
        suggestion_hidden,
        suggestion_verbose)] => diagnostics::diagnostic_derive
);

decl_derive!(
    [Subdiagnostic, attributes(
        // struct/variant attributes
        label,
        help,
        note,
        warning,
        suggestion,
        suggestion_short,
        suggestion_hidden,
        suggestion_verbose,
        multipart_suggestion,
        multipart_suggestion_short,
        multipart_suggestion_hidden,
        multipart_suggestion_verbose,
        // field attributes
        skip_arg,
        primary_span,
        suggestion_part,
        applicability)] => diagnostics::subdiagnostic_derive
);

decl_derive!(
    [TypeFoldable] => fold::type_foldable_derive
);

decl_derive!(
    [TypeVisitable] => fold::type_visitable_derive
);

#[proc_macro]
pub fn fluent_messages(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    diagnostics::fluent_messages(input)
}

#[proc_macro]
pub fn primop_rules(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    primops::primop_rules(input)
}
