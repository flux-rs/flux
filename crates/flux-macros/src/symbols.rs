//! This is based on the implementation of the `symbols` macro in rustc.

use std::collections::HashMap;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    Expr, Ident, Lit, LitStr, Result, Token, braced,
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

    let mut prefill_stream = quote! {};
    let mut entries = Entries::with_capacity(input.keywords.len());

    // Generate the listed keywords.
    let mut keyword_stream = quote! {};
    for keyword in &input.keywords {
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

    // Generate the listed symbols.
    let mut symbols_stream = quote! {};
    let mut prev_key: Option<(Span, String)> = None;
    let mut check_order = |span: Span, s: &str, errors: &mut Errors| {
        if let Some((prev_span, ref prev_str)) = prev_key
            && s < prev_str
        {
            errors.error(span, format!("Symbol `{s}` must precede `{prev_str}`"));
            errors.error(prev_span, format!("location of previous symbol `{prev_str}`"));
        }
        prev_key = Some((span, s.to_string()));
    };
    for symbol in &input.symbols {
        let name = &symbol.name;
        check_order(symbol.name.span(), &name.to_string(), &mut errors);
        let value = match &symbol.value {
            Value::SameAsName => name.to_string(),
            Value::String(lit) => lit.value(),
            Value::Unsupported(expr) => {
                errors.list.push(syn::Error::new_spanned(
                    expr,
                    concat!(
                        "unsupported expression for symbol value; implement support for this in ",
                        file!(),
                    ),
                ));
                continue;
            }
        };
        let idx = entries.insert(symbol.name.span(), &value, &mut errors);

        prefill_stream.extend(quote! {
            #value,
        });
        symbols_stream.extend(quote! {
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

        #[doc(hidden)]
        #[allow(non_upper_case_globals)]
        pub mod sym_generated {
            use rustc_span::Symbol;
            #symbols_stream
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

impl Parse for Keyword {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        let value = input.parse()?;

        Ok(Keyword { name, value })
    }
}

struct Symbol {
    name: Ident,
    value: Value,
}

enum Value {
    SameAsName,
    String(LitStr),
    Unsupported(Expr),
}

impl Parse for Symbol {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let name = input.parse()?;
        let colon_token: Option<Token![:]> = input.parse()?;
        let value = if colon_token.is_some() { input.parse()? } else { Value::SameAsName };

        Ok(Symbol { name, value })
    }
}

impl Parse for Value {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let expr: Expr = input.parse()?;
        if let Expr::Lit(expr) = &expr
            && let Lit::Str(lit) = &expr.lit
        {
            Ok(Value::String(lit.clone()))
        } else {
            Ok(Value::Unsupported(expr))
        }
    }
}

struct Input {
    keywords: Punctuated<Keyword, Token![,]>,
    symbols: Punctuated<Symbol, Token![,]>,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::Keywords>()?;
        let content;
        braced!(content in input);
        let keywords = Punctuated::parse_terminated(&content)?;

        input.parse::<kw::Symbols>()?;
        let content;
        braced!(content in input);
        let symbols = Punctuated::parse_terminated(&content)?;

        Ok(Input { keywords, symbols })
    }
}

mod kw {
    syn::custom_keyword!(Keywords);
    syn::custom_keyword!(Symbols);
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
