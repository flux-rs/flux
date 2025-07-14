use std::collections::HashMap;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    Ident, LitStr, Result, Token, braced,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

pub(super) fn symbols(input: TokenStream) -> TokenStream {
    let (mut output, errors) = symbols_with_errors(input);

    // If we generated any errors, then report them as compiler_error!() macro calls.
    // This lets the errors point back to the most relevant span. It also allows us
    // to report as many errors as we can during a single run.
    output.extend(errors.into_iter().map(|e| e.to_compile_error()));

    output
}

fn symbols_with_errors(input: TokenStream) -> (TokenStream, Vec<syn::Error>) {
    let mut errors = Errors::default();

    let input: Input = match syn::parse2(input) {
        Ok(input) => input,
        Err(e) => {
            errors.list.push(e);
            return (TokenStream::default(), errors.list);
        }
    };

    let mut keyword_stream = quote! {};
    let mut prefill_stream = quote! {};

    let mut entries = Entries::with_capacity(input.keywords.len());
    for keyword in input.keywords.iter() {
        let name = &keyword.name;
        let value = &keyword.value;
        let value_string = value.value();
        let idx = entries.insert(keyword.name.span(), &value_string, &mut errors);
        prefill_stream.extend(quote! {
            #value,
        });
        keyword_stream.extend(quote! {
            pub const #name: Symbol = Symbol::new(rustc_span::symbol::PREDEFINED_SYMBOLS_COUNT + #idx);
        });
    }

    let predefined_flux_symbols_count = entries.len();
    let predefined_flux_symbols_count_usize = predefined_flux_symbols_count as usize;
    let output = quote! {
        pub const PREDEFINED_FLUX_SYMBOLS_COUNT: u32 = #predefined_flux_symbols_count;

        #[doc(hidden)]
        #[allow(non_upper_case_globals)]
        mod kw_generated {
            use rustc_span::Symbol;

            #keyword_stream
        }

        pub const PREDEFINED_FLUX_SYMBOLS: [&'static str; #predefined_flux_symbols_count_usize] =
            [#prefill_stream];
    };
    (output, errors.list)
}

struct Keyword {
    name: Ident,
    value: LitStr,
}

struct Input {
    keywords: Punctuated<Keyword, Token![,]>,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::Keywords>()?;
        let content;
        braced!(content in input);
        let keywords = Punctuated::parse_terminated(&content)?;

        Ok(Input { keywords })
    }
}

impl Parse for Keyword {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        let value = input.parse()?;

        Ok(Keyword { name, value })
    }
}

mod kw {
    syn::custom_keyword!(Keywords);
}

#[derive(Default)]
struct Errors {
    list: Vec<syn::Error>,
}

impl Errors {
    fn error(&mut self, span: Span, message: String) {
        self.list.push(syn::Error::new(span, message));
    }
}

struct Entries {
    map: HashMap<String, Predefined>,
}

impl Entries {
    fn with_capacity(capacity: usize) -> Self {
        Entries { map: HashMap::with_capacity(capacity) }
    }

    fn insert(&mut self, span: Span, s: &str, errors: &mut Errors) -> u32 {
        if let Some(prev) = self.map.get(s) {
            errors.error(span, format!("Symbol `{s}` is duplicated"));
            errors.error(prev.span_of_name, "location of previous definition".to_string());
            prev.idx
        } else {
            let idx = self.len();
            self.map
                .insert(s.to_string(), Predefined { idx, span_of_name: span });
            idx
        }
    }

    fn len(&self) -> u32 {
        u32::try_from(self.map.len()).expect("way too many symbols")
    }
}

struct Predefined {
    idx: u32,
    span_of_name: Span,
}
