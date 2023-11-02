#[cfg(not(flux_sysroot))]
use attr_dummy as attr_impl;
#[cfg(flux_sysroot)]
use attr_sysroot as attr_impl;
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn alias(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::alias(attrs, tokens)
}

#[proc_macro_attribute]
pub fn sig(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::sig(attrs, tokens)
}

#[proc_macro_attribute]
pub fn qualifiers(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::qualifiers(attrs, tokens)
}

#[proc_macro_attribute]
pub fn refined_by(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::refined_by(attrs, tokens)
}

#[proc_macro_attribute]
pub fn invariant(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::invariant(attrs, tokens)
}

#[proc_macro_attribute]
pub fn constant(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::constant(attrs, tokens)
}

#[proc_macro_attribute]
pub fn ignore(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::ignore(attrs, tokens)
}

#[proc_macro_attribute]
pub fn opaque(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::opaque(attrs, tokens)
}

#[proc_macro_attribute]
pub fn trusted(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::trusted(attrs, tokens)
}

#[proc_macro]
pub fn flux(tokens: TokenStream) -> TokenStream {
    flux_attrs::flux(tokens.into()).into()
}

#[proc_macro_attribute]
pub fn extern_spec(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    attr_impl::extern_spec(attrs, tokens)
}

#[cfg(flux_sysroot)]
mod attr_sysroot {
    use super::*;

    pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        flux_attrs::extern_spec(attr.into(), tokens.into()).into()
    }

    macro_rules! flux_tool_attrs {
        ($($name:ident),+ $(,)?) => {
            $(
            pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
                flux_attrs::flux_tool_attr(stringify!($name), attr.into(), item.into()).into()
            }
            )*
        };
    }

    flux_tool_attrs!(alias, sig, qualifiers, constant, invariant, ignore, opaque, trusted);

    pub fn refined_by(attr: TokenStream, item: TokenStream) -> TokenStream {
        flux_attrs::flux_tool_adt_attr("refined_by", attr.into(), item.into()).into()
    }
}

#[cfg(not(flux_sysroot))]
mod attr_dummy {
    use super::*;

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
        alias,
        sig,
        qualifiers,
        refined_by,
        invariant,
        constant,
        ignore,
        opaque,
        trusted,
        extern_spec,
    );
}
