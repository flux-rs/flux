#[cfg(not(flux_sysroot))]
use attr_dummy as attr_impl;
#[cfg(flux_sysroot)]
use attr_sysroot as attr_impl;
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn alias(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::alias(attr, tokens)
}

#[proc_macro_attribute]
pub fn sig(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::sig(attr, tokens)
}

#[proc_macro_attribute]
pub fn spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::spec(attr, tokens)
}

#[proc_macro_attribute]
pub fn qualifiers(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::qualifiers(attr, tokens)
}

#[proc_macro_attribute]
pub fn refined_by(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::refined_by(attr, tokens)
}

#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::invariant(attr, tokens)
}

#[proc_macro_attribute]
pub fn constant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::constant(attr, tokens)
}

#[proc_macro_attribute]
pub fn opaque(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::opaque(attr, tokens)
}

#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::trusted(attr, tokens)
}

#[proc_macro_attribute]
pub fn generics(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::generics(attr, tokens)
}

#[proc_macro_attribute]
pub fn assoc(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::assoc(attr, tokens)
}

#[proc_macro]
pub fn flux(tokens: TokenStream) -> TokenStream {
    flux_attrs::flux(tokens.into()).into()
}

#[proc_macro]
pub fn defs(tokens: TokenStream) -> TokenStream {
    attr_impl::defs(tokens)
}

#[proc_macro_attribute]
pub fn extern_spec(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::extern_spec(attrs, tokens)
}

#[proc_macro_attribute]
pub fn ignore(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::ignore(attrs, tokens)
}

#[cfg(flux_sysroot)]
mod attr_sysroot {
    use super::*;

    pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        flux_attrs::extern_spec(attr.into(), tokens.into()).into()
    }

    pub fn refined_by(attr: TokenStream, item: TokenStream) -> TokenStream {
        flux_attrs::refined_by(attr.into(), item.into()).into()
    }

    pub fn defs(tokens: TokenStream) -> TokenStream {
        flux_attrs::defs(tokens.into()).into()
    }

    macro_rules! flux_tool_attrs {
        ($($name:ident),+ $(,)?) => {
            $(
            pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
                flux_attrs::flux_tool_item_attr(stringify!($name), attr.into(), item.into()).into()
            }
            )*
        };
    }

    flux_tool_attrs!(
        alias, spec, sig, qualifiers, constant, invariant, opaque, trusted, generics, assoc, ignore
    );
}

#[cfg(not(flux_sysroot))]
mod attr_dummy {
    use super::*;

    pub fn refined_by(attr: TokenStream, item: TokenStream) -> TokenStream {
        flux_attrs::refined_by(attr.into(), item.into()).into()
    }

    pub fn defs(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    pub fn extern_spec(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    macro_rules! no_op {
        ($($name:ident),+ $(,)?) => {
            $(
            pub fn $name(_attr: TokenStream, item: TokenStream) -> TokenStream {
                item
            }
            )+
        };
    }

    no_op!(
        alias, spec, sig, qualifiers, invariant, constant, opaque, trusted, generics, assoc, ignore
    );
}
