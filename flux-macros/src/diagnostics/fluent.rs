use annotate_snippets::{
    display_list::DisplayList,
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};
use fluent_bundle::{FluentBundle, FluentError, FluentResource};
use fluent_syntax::{
    ast::{Attribute, Entry, Identifier, Message},
    parser::ParserError,
};
use proc_macro::{Diagnostic, Level, Span};
use proc_macro2::TokenStream;
use quote::quote;
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token, Ident, LitStr, Result,
};
use unic_langid::langid;

struct Resource {
    ident: Ident,
    #[allow(dead_code)]
    fat_arrow_token: token::FatArrow,
    resource: LitStr,
}

impl Parse for Resource {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        Ok(Resource {
            ident: input.parse()?,
            fat_arrow_token: input.parse()?,
            resource: input.parse()?,
        })
    }
}

struct Resources(Punctuated<Resource, token::Comma>);

impl Parse for Resources {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let mut resources = Punctuated::new();
        loop {
            if input.is_empty() || input.peek(token::Brace) {
                break;
            }
            let value = input.parse()?;
            resources.push_value(value);
            if !input.peek(token::Comma) {
                break;
            }
            let punct = input.parse()?;
            resources.push_punct(punct);
        }
        Ok(Resources(resources))
    }
}

/// Helper function for returning an absolute path for macro-invocation relative file paths.
///
/// If the input is already absolute, then the input is returned. If the input is not absolute,
/// then it is appended to the directory containing the source file with this macro invocation.
fn invocation_relative_path_to_absolute(span: Span, path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        // `/a/b/c/foo/bar.rs` contains the current macro invocation
        let mut source_file_path = span.source_file().path();
        // `/a/b/c/foo/`
        source_file_path.pop();
        // `/a/b/c/foo/../locales/en-US/example.ftl`
        source_file_path.push(path);
        source_file_path
    }
}

/// See [rustc_macros::fluent_messages].
pub(crate) fn fluent_messages(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let resources = parse_macro_input!(input as Resources);

    // Cannot iterate over individual messages in a bundle, so do that using the
    // `FluentResource` instead. Construct a bundle anyway to find out if there are conflicting
    // messages in the resources.
    let mut bundle = FluentBundle::new(vec![langid!("en-US")]);

    // Map of Fluent identifiers to the `Span` of the resource that defined them, used for better
    // diagnostics.
    let mut previous_defns = HashMap::new();

    let mut includes = TokenStream::new();
    let mut generated = TokenStream::new();
    for res in resources.0 {
        let ident_span = res.ident.span().unwrap();
        let path_span = res.resource.span().unwrap();

        // Set of Fluent attribute names already output, to avoid duplicate type errors - any given
        // constant created for a given attribute is the same.
        let mut previous_attrs = HashSet::new();

        let relative_ftl_path = res.resource.value();
        let absolute_ftl_path =
            invocation_relative_path_to_absolute(ident_span, &relative_ftl_path);
        // As this macro also outputs an `include_str!` for this file, the macro will always be
        // re-executed when the file changes.
        let mut resource_file = match File::open(absolute_ftl_path) {
            Ok(resource_file) => resource_file,
            Err(e) => {
                Diagnostic::spanned(path_span, Level::Error, "could not open Fluent resource")
                    .note(e.to_string())
                    .emit();
                continue;
            }
        };
        let mut resource_contents = String::new();
        if let Err(e) = resource_file.read_to_string(&mut resource_contents) {
            Diagnostic::spanned(path_span, Level::Error, "could not read Fluent resource")
                .note(e.to_string())
                .emit();
            continue;
        }
        let resource = match FluentResource::try_new(resource_contents) {
            Ok(resource) => resource,
            Err((this, errs)) => {
                Diagnostic::spanned(path_span, Level::Error, "could not parse Fluent resource")
                    .help("see additional errors emitted")
                    .emit();
                for ParserError { pos, slice: _, kind } in errs {
                    let mut err = kind.to_string();
                    // Entirely unnecessary string modification so that the error message starts
                    // with a lowercase as rustc errors do.
                    err.replace_range(
                        0..1,
                        &err.chars().next().unwrap().to_lowercase().to_string(),
                    );

                    let line_starts: Vec<usize> = std::iter::once(0)
                        .chain(
                            this.source()
                                .char_indices()
                                .filter_map(|(i, c)| Some(i + 1).filter(|_| c == '\n')),
                        )
                        .collect();
                    let line_start = line_starts
                        .iter()
                        .enumerate()
                        .map(|(line, idx)| (line + 1, idx))
                        .filter(|(_, idx)| **idx <= pos.start)
                        .last()
                        .unwrap()
                        .0;

                    let snippet = Snippet {
                        title: Some(Annotation {
                            label: Some(&err),
                            id: None,
                            annotation_type: AnnotationType::Error,
                        }),
                        footer: vec![],
                        slices: vec![Slice {
                            source: this.source(),
                            line_start,
                            origin: Some(&relative_ftl_path),
                            fold: true,
                            annotations: vec![SourceAnnotation {
                                label: "",
                                annotation_type: AnnotationType::Error,
                                range: (pos.start, pos.end - 1),
                            }],
                        }],
                        opt: Default::default(),
                    };
                    let dl = DisplayList::from(snippet);
                    eprintln!("{}\n", dl);
                }
                continue;
            }
        };

        let mut constants = TokenStream::new();
        for entry in resource.entries() {
            let span = res.ident.span();
            if let Entry::Message(Message { id: Identifier { name }, attributes, .. }) = entry {
                let _ = previous_defns.entry(name.to_string()).or_insert(ident_span);

                // `typeck-foo-bar` => `foo_bar` (in `typeck.ftl`)
                // `const-eval-baz` => `baz` (in `const_eval.ftl`)
                let snake_name = Ident::new(
                    // FIXME: should probably trim prefix, not replace all occurrences
                    &name
                        .replace(&format!("{}-", res.ident).replace('_', "-"), "")
                        .replace('-', "_"),
                    span,
                );
                constants.extend(quote! {
                    pub const #snake_name: crate::DiagnosticMessage =
                        crate::DiagnosticMessage::FluentIdentifier(
                            std::borrow::Cow::Borrowed(#name),
                            None
                        );
                });

                for Attribute { id: Identifier { name: attr_name }, .. } in attributes {
                    let snake_name = Ident::new(&attr_name.replace('-', "_"), span);
                    if !previous_attrs.insert(snake_name.clone()) {
                        continue;
                    }

                    constants.extend(quote! {
                        pub const #snake_name: crate::SubdiagnosticMessage =
                            crate::SubdiagnosticMessage::FluentAttr(
                                std::borrow::Cow::Borrowed(#attr_name)
                            );
                    });
                }
            }
        }

        if let Err(errs) = bundle.add_resource(resource) {
            for e in errs {
                match e {
                    FluentError::Overriding { kind, id } => {
                        Diagnostic::spanned(
                            ident_span,
                            Level::Error,
                            format!("overrides existing {}: `{}`", kind, id),
                        )
                        .span_help(previous_defns[&id], "previously defined in this resource")
                        .emit();
                    }
                    FluentError::ResolverError(_) | FluentError::ParserError(_) => unreachable!(),
                }
            }
        }

        includes.extend(quote! { include_str!(#relative_ftl_path), });

        let ident = res.ident;
        generated.extend(quote! {
            pub mod #ident {
                #constants
            }
        });
    }

    quote! {
        #[allow(non_upper_case_globals)]
        #[doc(hidden)]
        pub mod fluent_generated {
            pub static DEFAULT_LOCALE_RESOURCES: &'static [&'static str] = &[
                #includes
            ];

            #generated

            pub mod _subdiag {
                pub const help: crate::SubdiagnosticMessage =
                    crate::SubdiagnosticMessage::FluentAttr(std::borrow::Cow::Borrowed("help"));
                pub const note: crate::SubdiagnosticMessage =
                    crate::SubdiagnosticMessage::FluentAttr(std::borrow::Cow::Borrowed("note"));
                pub const warn: crate::SubdiagnosticMessage =
                    crate::SubdiagnosticMessage::FluentAttr(std::borrow::Cow::Borrowed("warn"));
                pub const label: crate::SubdiagnosticMessage =
                    crate::SubdiagnosticMessage::FluentAttr(std::borrow::Cow::Borrowed("label"));
                pub const suggestion: crate::SubdiagnosticMessage =
                    crate::SubdiagnosticMessage::FluentAttr(std::borrow::Cow::Borrowed("suggestion"));
            }
        }
    }
    .into()
}
