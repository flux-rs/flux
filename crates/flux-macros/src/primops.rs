use std::collections::HashMap;

use itertools::Itertools;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token, Ident, Lifetime, Token,
};

macro_rules! unwrap_result {
    ($e:expr) => {{
        match $e {
            Ok(e) => e,
            Err(e) => return e.to_compile_error().into(),
        }
    }};
}

pub fn primop_rules(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let rules = parse_macro_input!(input as Rules);

    let argc = unwrap_result!(rules.check_arg_count());

    let rules = rules.0.into_iter().enumerate().map(|(i, rule)| {
        Renderer::new(i, rule)
            .render()
            .unwrap_or_else(|err| err.to_compile_error())
    });
    let args = args(argc);
    quote! {
        #[allow(unused_variables, non_snake_case)]
        |#args| {
            #(#rules)*
            None
        }
    }
    .into()
}

fn args(n: usize) -> TokenStream {
    let args = (0..n).map(|i| {
        let bty = mk_bty_arg(i);
        let idx = mk_idx_arg(i);
        quote!((#bty, #idx))
    });
    quote!([#(#args),*])
}

struct Rules(Vec<Rule>);

impl Rules {
    /// Check that the number of arguments is the same in all rules
    fn check_arg_count(&self) -> syn::Result<usize> {
        let argc = self.0.first().map(|rule| rule.args.len()).unwrap_or(0);
        for rule in &self.0 {
            if rule.args.len() != argc {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "all rules must have the same number of arguments",
                ));
            }
        }
        Ok(argc)
    }
}

impl Parse for Rules {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut v = vec![];
        while !input.is_empty() {
            v.push(input.parse()?);
        }
        Ok(Rules(v))
    }
}

struct Renderer {
    lbl: Lifetime,
    rule: Rule,
    /// The set of metavars and the index of the inputs they match
    metavars: HashMap<String, Vec<usize>>,
}

impl Renderer {
    fn new(i: usize, rule: Rule) -> Self {
        let mut metavars: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, input) in rule.args.iter().enumerate() {
            let bty_str = input.bty.to_string();
            if !is_primitive_type(&bty_str) {
                metavars.entry(bty_str).or_default().push(i);
            }
        }

        let lbl = syn::Lifetime::new(&format!("'lbl{}", i), Span::call_site());

        Self { lbl, rule, metavars }
    }

    fn render(&self) -> syn::Result<TokenStream> {
        let lbl = &self.lbl;
        let metavar_matching = self.metavar_matching();
        let primitive_checks = self.check_primitive_types();
        let declare_metavars = self.declare_metavars();
        let guards = self.guards();
        let declare_idxs_names = self.declare_idxs_names();
        let output_type = self.output_type()?;
        let precondition = self.precondition();
        Ok(quote! {
            #lbl: {
                #metavar_matching
                #primitive_checks
                #declare_metavars
                #guards

                #declare_idxs_names
                let precondition = #precondition;
                let v = Expr::nu();
                let output_type = #output_type;
                return Some(MatchedRule { precondition, output_type })
            }
        })
    }

    fn bty_arg_or_prim(&self, ident: &syn::Ident) -> syn::Result<TokenStream> {
        let ident_str = ident.to_string();
        if is_primitive_type(ident) {
            Ok(quote!(BaseTy::from_primitive_str(#ident_str).unwrap()))
        } else {
            self.metavars
                .get(&ident_str)
                .map(|idxs| {
                    let arg = mk_bty_arg(idxs[0]);
                    quote!(#arg.clone())
                })
                .ok_or_else(|| {
                    syn::Error::new(ident.span(), format!("cannot find metavariable `{ident_str}`"))
                })
        }
    }

    fn output_type(&self) -> syn::Result<TokenStream> {
        let out = match &self.rule.output {
            Output::Base(bty) => {
                let bty = self.bty_arg_or_prim(bty)?;
                quote!(#bty.to_ty())
            }
            Output::Indexed(bty, idx) => {
                let bty = self.bty_arg_or_prim(bty)?;
                quote!(rty::Ty::indexed( #bty, #idx))
            }
            Output::Exists(bty, pred) => {
                let bty = self.bty_arg_or_prim(bty)?;
                quote!(rty::Ty::exists_with_constr( #bty, #pred))
            }
        };
        Ok(out)
    }

    /// Generates the code that checks that all the inputs matching the same metavariable are equal
    fn metavar_matching(&self) -> TokenStream {
        let lbl = &self.lbl;
        let checks = self.metavars.values().map(|idxs| {
            let checks = idxs.iter().tuple_windows().map(|(i, j)| {
                let bty_arg1 = mk_bty_arg(*i);
                let bty_arg2 = mk_bty_arg(*j);
                quote! {
                    if #bty_arg2 != #bty_arg1 {
                        break #lbl;
                    }
                }
            });
            quote!(#(#checks)*)
        });
        quote!(#(#checks)*)
    }

    /// Generates the code that checks if an arg matching a primitive type has indeed that type
    fn check_primitive_types(&self) -> TokenStream {
        let lbl = &self.lbl;
        self.rule
            .args
            .iter()
            .enumerate()
            .flat_map(|(i, arg)| {
                let bty = &arg.bty;
                if is_primitive_type(bty) {
                    let bty_str = bty.to_string();
                    let bty_arg = mk_bty_arg(i);
                    Some(quote! {
                        let Some(s) = #bty_arg.primitive_symbol() else {
                            break #lbl;
                        };
                        if s.as_str() != #bty_str {
                            break #lbl;
                        }
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    fn precondition(&self) -> TokenStream {
        if let Some(requires) = &self.rule.requires {
            let reason = &requires.reason;
            let pred = &requires.pred;
            quote!(Some(Pre { reason: #reason, pred: #pred }))
        } else {
            quote!(None)
        }
    }

    /// Declare metavars as variables so they can be accessed in the guards
    fn declare_metavars(&self) -> TokenStream {
        self.metavars
            .iter()
            .map(|(var, matching_positions)| {
                let var = syn::Ident::new(var, Span::call_site());
                let bty_arg = mk_bty_arg(matching_positions[0]);
                quote! {
                    let #var = #bty_arg;
                }
            })
            .collect()
    }

    fn declare_idxs_names(&self) -> TokenStream {
        self.rule
            .args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let name = &arg.name;
                let idx_arg = mk_idx_arg(i);
                quote!(let #name = #idx_arg;)
            })
            .collect()
    }

    fn guards(&self) -> TokenStream {
        self.rule
            .guards
            .iter()
            .map(|guard| self.guard(guard))
            .collect()
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

struct Rule {
    args: Punctuated<Arg, Token![,]>,
    output: Output,
    requires: Option<Requires>,
    guards: Vec<Guard>,
}

impl Parse for Rule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _: Token![fn] = input.parse()?;
        let content;
        parenthesized!(content in input);
        let inputs = content.parse_terminated(Arg::parse, Token![,])?;
        let _: Token![->] = input.parse()?;
        let output = input.parse()?;
        let requires = if input.peek(kw::requires) { Some(input.parse()?) } else { None };
        let guards = parse_guards(input)?;
        Ok(Rule { args: inputs, output, requires, guards })
    }
}

/// An arg of the form `a: T`
struct Arg {
    name: syn::Ident,
    bty: syn::Ident,
}

impl Parse for Arg {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        let _: Token![:] = input.parse()?;
        let bty = input.parse()?;
        Ok(Arg { name, bty })
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
    reason: syn::Path,
}

impl Parse for Requires {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _: kw::requires = input.parse()?;
        let pred = input.parse()?;
        let _: Token![=>] = input.parse()?;
        let reason = input.parse()?;
        Ok(Requires { pred, reason })
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

fn mk_idx_arg(i: usize) -> Ident {
    Ident::new(&format!("idx{}", i), Span::call_site())
}

fn mk_bty_arg(i: usize) -> Ident {
    Ident::new(&format!("bty{}", i), Span::call_site())
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
