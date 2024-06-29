use std::collections::HashMap;

use itertools::Itertools;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token, Lifetime, Token,
};

pub fn signatures(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let sigs = parse_macro_input!(input as PrimOpSigs);
    let sigs = sigs.0.into_iter().enumerate().map(|(i, sig)| {
        Renderer::new(i, sig)
            .render()
            .unwrap_or_else(|err| err.to_compile_error())
    });
    quote! {
        PrimOpFactory {
            #[allow(unused_variables, non_snake_case)]
            make: |inputs| {
                #(#sigs)*
                None
            },
        }
    }
    .into()
}

struct PrimOpSigs(Vec<Sig>);

impl Parse for PrimOpSigs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut v = vec![];
        while !input.is_empty() {
            v.push(input.parse()?);
        }
        Ok(PrimOpSigs(v))
    }
}

struct Renderer {
    lbl: Lifetime,
    sig: Sig,
    /// The set of metavars and the index of the inputs they match
    metavars: HashMap<String, Vec<usize>>,
    args: TokenStream,
}

impl Renderer {
    fn new(i: usize, sig: Sig) -> Self {
        let mut metavars: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, input) in sig.inputs.iter().enumerate() {
            let bty_str = input.bty.to_string();
            if !is_primitive_type(&bty_str) {
                metavars.entry(bty_str).or_default().push(i);
            }
        }

        let args = sig.inputs.iter().map(|input| &input.name);
        let args = quote!([#(#args),*]);

        let lbl = syn::Lifetime::new(&format!("'lbl{}", i), Span::call_site());

        Self { lbl, sig, metavars, args }
    }

    fn render(&self) -> syn::Result<TokenStream> {
        let lbl = &self.lbl;
        let metavar_matching = self.metavar_matching();
        let primitive_checks = self.check_primitive_types();
        let declare_metavars = self.declare_metavars();
        let guards = self.guards();
        let output = self.render_output()?;
        let requires = self.requires();
        Ok(quote! {
            #lbl: {
                #metavar_matching
                #primitive_checks
                #declare_metavars
                #guards

                let out = #output;
                return Some(PrimOpSig {
                    pre: #requires,
                    out,
                })
            }
        })
    }

    fn render_bty(&self, ident: &syn::Ident) -> syn::Result<TokenStream> {
        let ident_str = ident.to_string();
        if is_primitive_type(ident) {
            Ok(quote!(BaseTy::from_primitive_str(#ident_str).unwrap()))
        } else {
            self.metavars
                .get(&ident_str)
                .map(|idxs| {
                    let i = idxs[0];
                    quote!(inputs[#i].clone())
                })
                .ok_or_else(|| {
                    syn::Error::new(ident.span(), format!("cannot find metavariable `{ident_str}`"))
                })
        }
    }

    fn render_output(&self) -> syn::Result<TokenStream> {
        let out = match &self.sig.output {
            Output::Base(bty) => {
                let bty = self.render_bty(bty)?;
                quote!(Output::Base(#bty))
            }
            Output::Indexed(bty, mk_expr) => {
                let bty = self.render_bty(bty)?;
                let args = &self.args;
                quote! {
                    Output::Indexed(
                        #bty,
                        |#args| #mk_expr,
                    )
                }
            }
            Output::Exists(bty, mk_pred) => {
                let bty = self.render_bty(bty)?;
                let args = &self.args;
                quote! {
                    Output::Exists(
                        #bty,
                        |v, #args| #mk_pred,
                    )
                }
            }
        };
        Ok(out)
    }

    /// Generates the code that checks that all the inputs matching the same metavariable are equal
    fn metavar_matching(&self) -> TokenStream {
        let lbl = &self.lbl;
        let checks = self.metavars.values().map(|idxs| {
            let checks = idxs.iter().tuple_windows().map(|(i, j)| {
                quote! {
                    if inputs[#i] != inputs[#j] {
                        break #lbl;
                    }
                }
            });
            quote!(#(#checks)*)
        });
        quote!(#(#checks)*)
    }

    /// Generates the code that checks if an input matching a primitive type has indeed that type
    fn check_primitive_types(&self) -> TokenStream {
        let lbl = &self.lbl;
        let checks = self.sig.inputs.iter().enumerate().flat_map(|(i, input)| {
            let bty = &input.bty;
            if is_primitive_type(bty) {
                let bty_str = bty.to_string();
                Some(quote! {
                    let Some(s) = inputs[#i].primitive_symbol() else {
                        break #lbl;
                    };
                    if s.as_str() != #bty_str {
                        break #lbl;
                    }
                })
            } else {
                None
            }
        });
        quote!(#(#checks)*)
    }

    fn requires(&self) -> TokenStream {
        if let Some(requires) = &self.sig.requires {
            let tag = &requires.tag;
            let pred = &requires.pred;
            let args = &self.args;
            quote!(Pre::Some(#tag, Box::new(move |#args| #pred)))
        } else {
            quote!(Pre::None)
        }
    }

    /// Declare metavars as variables so they can be accessed in the guards
    fn declare_metavars(&self) -> TokenStream {
        let metavars = self.metavars.iter().map(|(var, idxs)| {
            let i = idxs[0];
            let var = syn::Ident::new(var, Span::call_site());
            quote! {
                let #var = &inputs[#i];
            }
        });
        quote!(#(#metavars)*)
    }

    fn guards(&self) -> TokenStream {
        let guards = self.sig.guards.iter().map(|guard| self.guard(guard));
        quote!(#(#guards)*)
    }

    fn guard(&self, guard: &Guard) -> TokenStream {
        let lbl = &self.lbl;
        match guard {
            Guard::If(if_, expr) => quote! {#if_ !(#expr) { break #lbl; }},
            Guard::IfLet(let_) => quote!(#let_ else { break #lbl; };),
            Guard::Let(let_) => quote!(#let_;),
        }
    }
}

struct Sig {
    inputs: Punctuated<Input, Token![,]>,
    output: Output,
    requires: Option<Requires>,
    guards: Vec<Guard>,
}

impl Parse for Sig {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _: Token![fn] = input.parse()?;
        let content;
        parenthesized!(content in input);
        let inputs = content.parse_terminated(Input::parse, Token![,])?;
        let _: Token![->] = input.parse()?;
        let output = input.parse()?;
        let requires = if input.peek(kw::requires) { Some(input.parse()?) } else { None };
        let guards = parse_guards(input)?;
        Ok(Sig { inputs, output, requires, guards })
    }
}

/// An input of the form `a: T`
struct Input {
    name: syn::Ident,
    bty: syn::Ident,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        let _: Token![:] = input.parse()?;
        let bty = input.parse()?;
        Ok(Input { name, bty })
    }
}

enum Output {
    Base(syn::Ident),
    Indexed(syn::Ident, TokenStream),
    Exists(syn::Ident, TokenStream),
}

impl Parse for Output {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let bty: syn::Ident = input.parse()?;
        if input.peek(token::Bracket) {
            let content;
            bracketed!(content in input);
            Ok(Output::Indexed(bty, content.parse()?))
        } else if input.peek(token::Brace) {
            let content;
            braced!(content in input);
            let _: syn::Ident = content.parse()?;
            let _: Token![:] = content.parse()?;
            Ok(Output::Exists(bty, content.parse()?))
        } else {
            Ok(Output::Base(bty))
        }
    }
}

struct Requires {
    pred: syn::Expr,
    tag: syn::Path,
}

impl Parse for Requires {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _: kw::requires = input.parse()?;
        let pred = input.parse()?;
        let _: Token![=>] = input.parse()?;
        let tag = input.parse()?;
        Ok(Requires { pred, tag })
    }
}

fn parse_guards(input: ParseStream) -> syn::Result<Vec<Guard>> {
    let mut guards = vec![];
    while !input.is_empty() && (input.peek(Token![let]) || input.peek(Token![if])) {
        guards.push(input.parse()?);
    }
    Ok(guards)
}
enum Guard {
    If(Token![if], syn::Expr),
    IfLet(syn::ExprLet),
    Let(syn::ExprLet),
}

impl Parse for Guard {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![if]) {
            let if_ = input.parse()?;
            if input.peek(Token![let]) {
                Ok(Guard::IfLet(input.parse()?))
            } else {
                Ok(Guard::If(if_, input.parse()?))
            }
        } else if lookahead.peek(Token![let]) {
            Ok(Guard::Let(input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

fn is_primitive_type<T>(s: &T) -> bool
where
    T: PartialEq<str>,
{
    s == "i8"
        || s == "i16"
        || s == "i32"
        || s == "i64"
        || s == "i128"
        || s == "u8"
        || s == "u16"
        || s == "u32"
        || s == "u64"
        || s == "u128"
        || s == "f32"
        || s == "f64"
        || s == "isize"
        || s == "usize"
        || s == "bool"
        || s == "char"
        || s == "str"
}

mod kw {
    syn::custom_keyword!(requires);
}
