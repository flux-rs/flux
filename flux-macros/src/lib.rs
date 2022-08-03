#![feature(proc_macro_diagnostic, never_type, let_else, proc_macro_span)]

mod diagnostics;

use proc_macro::TokenStream;
use synstructure::decl_derive;

decl_derive!(
    [SessionDiagnostic, attributes(
        // struct attributes
        warning,
        error,
        lint,
        help,
        note,
        warn_,
        // field attributes
        skip_arg,
        primary_span,
        label,
        subdiagnostic,
        suggestion,
        suggestion_short,
        suggestion_hidden,
        suggestion_verbose)] => diagnostics::session_diagnostic_derive
);

#[proc_macro]
pub fn fluent_messages(input: TokenStream) -> TokenStream {
    diagnostics::fluent_messages(input)
}
