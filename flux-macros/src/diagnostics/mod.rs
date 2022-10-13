#![allow(dead_code)]
#![allow(clippy::all)]

mod diagnostic;
mod diagnostic_builder;
mod error;
mod fluent;
mod utils;

use diagnostic::DiagnosticDerive;
pub(crate) use fluent::fluent_messages;
use proc_macro2::TokenStream;
use quote::format_ident;
use synstructure::Structure;

pub fn diagnostic_derive(s: Structure<'_>) -> TokenStream {
    DiagnosticDerive::new(format_ident!("diag"), format_ident!("sess"), s).into_tokens()
}
