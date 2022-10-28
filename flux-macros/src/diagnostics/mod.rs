#![allow(dead_code)]
#![allow(clippy::all)]

mod diagnostic;
mod diagnostic_builder;
mod error;
mod fluent;
mod subdiagnostic;
mod utils;

use diagnostic::DiagnosticDerive;
pub(crate) use fluent::fluent_messages;
use proc_macro2::TokenStream;
use quote::format_ident;
use subdiagnostic::SubdiagnosticDerive;
use synstructure::Structure;

pub fn diagnostic_derive(s: Structure<'_>) -> TokenStream {
    DiagnosticDerive::new(format_ident!("diag"), format_ident!("sess"), s).into_tokens()
}

pub fn subdiagnostic_derive(s: Structure<'_>) -> TokenStream {
    SubdiagnosticDerive::new(s).into_tokens()
}
