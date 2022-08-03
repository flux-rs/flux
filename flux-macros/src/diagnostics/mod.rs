mod diagnostic;
mod diagnostic_builder;
mod error;
mod fluent;
mod utils;

use diagnostic::SessionDiagnosticDerive;
pub(crate) use fluent::fluent_messages;
use proc_macro2::TokenStream;
use quote::format_ident;
use synstructure::Structure;

pub fn session_diagnostic_derive(s: Structure<'_>) -> TokenStream {
    SessionDiagnosticDerive::new(format_ident!("diag"), format_ident!("sess"), s).into_tokens()
}
