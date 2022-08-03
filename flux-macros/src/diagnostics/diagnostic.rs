#![deny(unused_must_use)]

use crate::diagnostics::{
    diagnostic_builder::{DiagnosticDeriveBuilder, DiagnosticDeriveKind},
    error::{span_err, DiagnosticDeriveError},
    utils::{build_field_mapping, SetOnce},
};
use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use synstructure::Structure;

/// The central struct for constructing the `into_diagnostic` method from an annotated struct.
pub(crate) struct SessionDiagnosticDerive<'a> {
    structure: Structure<'a>,
    sess: syn::Ident,
    builder: DiagnosticDeriveBuilder,
}

impl<'a> SessionDiagnosticDerive<'a> {
    pub(crate) fn new(diag: syn::Ident, sess: syn::Ident, structure: Structure<'a>) -> Self {
        Self {
            builder: DiagnosticDeriveBuilder {
                diag,
                fields: build_field_mapping(&structure),
                kind: None,
                code: None,
                slug: None,
            },
            sess,
            structure,
        }
    }

    pub(crate) fn into_tokens(self) -> TokenStream {
        let SessionDiagnosticDerive { mut structure, sess, mut builder } = self;

        let ast = structure.ast();
        let (implementation, param_ty) = {
            if let syn::Data::Struct(..) = ast.data {
                let preamble = builder.preamble(&structure);
                let (attrs, args) = builder.body(&mut structure);

                let span = ast.span().unwrap();
                let diag = &builder.diag;
                let init = match (builder.kind.value(), builder.slug.value()) {
                    (None, _) => {
                        span_err(span, "diagnostic kind not specified")
                            .help("use the `#[error(...)]` attribute to create an error")
                            .emit();
                        return DiagnosticDeriveError::ErrorHandled.into_compile_error();
                    }
                    (Some(kind), None) => {
                        span_err(span, "diagnostic slug not specified")
                            .help(&format!(
                                "specify the slug as the first argument to the attribute, such as \
                                 `#[{}(typeck::example_error)]`",
                                kind.descr()
                            ))
                            .emit();
                        return DiagnosticDeriveError::ErrorHandled.into_compile_error();
                    }
                    (Some(DiagnosticDeriveKind::Lint), _) => {
                        span_err(span, "only `#[error(..)]` and `#[warning(..)]` are supported")
                            .help("use the `#[error(...)]` attribute to create a error")
                            .emit();
                        return DiagnosticDeriveError::ErrorHandled.into_compile_error();
                    }
                    (Some(DiagnosticDeriveKind::Error), Some(slug)) => {
                        quote! {
                            let mut #diag = #sess.struct_err(flux_errors::fluent::#slug);
                        }
                    }
                    (Some(DiagnosticDeriveKind::Warn), Some(slug)) => {
                        quote! {
                            let mut #diag = #sess.struct_warn(flux_errors::fluent::#slug);
                        }
                    }
                };

                let implementation = quote! {
                    #init
                    #preamble
                    match self {
                        #attrs
                    }
                    match self {
                        #args
                    }
                    #diag
                };
                let param_ty = match builder.kind {
                    Some((DiagnosticDeriveKind::Error, _)) => {
                        quote! { flux_errors::ErrorGuaranteed }
                    }
                    Some((DiagnosticDeriveKind::Lint | DiagnosticDeriveKind::Warn, _)) => {
                        quote! { () }
                    }
                    _ => unreachable!(),
                };

                (implementation, param_ty)
            } else {
                span_err(
                    ast.span().unwrap(),
                    "`#[derive(SessionDiagnostic)]` can only be used on structs",
                )
                .emit();

                let implementation = DiagnosticDeriveError::ErrorHandled.into_compile_error();
                let param_ty = quote! { flux_errors::ErrorGuaranteed };
                (implementation, param_ty)
            }
        };

        structure.gen_impl(quote! {
            gen impl<'__session_diagnostic_sess> rustc_session::SessionDiagnostic<'__session_diagnostic_sess, #param_ty>
                    for @Self
            {
                fn into_diagnostic(
                    self,
                    #sess: &'__session_diagnostic_sess rustc_session::parse::ParseSess
                ) -> rustc_errors::DiagnosticBuilder<'__session_diagnostic_sess, #param_ty> {
                    use rustc_errors::IntoDiagnosticArg;
                    #implementation
                }
            }
        })
    }
}
