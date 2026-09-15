#![feature(proc_macro_diagnostic, never_type, proc_macro_tracked_path)]

#[allow(clippy::semicolon_if_nothing_returned)] // upstream code in `diagnostics::inline`
mod diagnostics;
mod fold;
mod primops;
mod symbols;

use quote::quote;
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
    [InlineDiagnostic, attributes(
        // struct and field attributes
        diag,
        help,
        help_once,
        note,
        note_once,
        warning,
        // field attributes
        primary_span,
        label,
        subdiagnostic,
        suggestion,
        suggestion_short,
        suggestion_hidden,
        suggestion_verbose)] => diagnostics::inline_diagnostic_derive
);

decl_derive!(
    [InlineSubdiagnostic, attributes(
        // struct/variant attributes
        label,
        help,
        help_once,
        note,
        note_once,
        warning,
        subdiagnostic,
        suggestion,
        suggestion_short,
        suggestion_hidden,
        suggestion_verbose,
        multipart_suggestion,
        multipart_suggestion_short,
        multipart_suggestion_hidden,
        // field attributes
        primary_span,
        suggestion_part,
        applicability)] => diagnostics::inline_subdiagnostic_derive
);

/// Creates a `DiagMessage` from an inline Fluent pattern. The pattern is checked to be valid
/// Fluent, but variables are not checked against the arguments set on the diagnostic.
#[proc_macro]
pub fn msg(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    diagnostics::msg_macro(input)
}

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

decl_derive!(
    [DebugAsJson] => debug_as_json
);

fn debug_as_json(s: synstructure::Structure<'_>) -> proc_macro2::TokenStream {
    s.gen_impl(quote! {
        gen impl std::fmt::Debug for @Self {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = serde_json::to_string(&self).map_err(|_| std::fmt::Error::default())?;
                write!(f, "{}", s)
            }
        }
    })
}

#[proc_macro]
pub fn symbols(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    symbols::symbols(input.into()).into()
}
