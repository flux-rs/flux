use quote::quote;
// use syn::parse_quote;

pub(crate) fn type_foldable_derive(mut s: synstructure::Structure<'_>) -> proc_macro2::TokenStream {
    if let syn::Data::Union(_) = s.ast().data {
        panic!("cannot derive on union")
    }

    // if !s.ast().generics.type_params().any(|ty| ty.ident == "I") {
    //     s.add_impl_generic(parse_quote! { I });
    // }

    // s.add_where_predicate(parse_quote! { I: Interner });
    s.add_bounds(synstructure::AddBounds::Fields);
    s.bind_with(|_| synstructure::BindStyle::Move);
    let body_fold = s.each_variant(|vi| {
        let bindings = vi.bindings();
        vi.construct(|_, index| {
            let bind = &bindings[index];
            quote! {
                ::flux_middle::rty::fold::TypeFoldable::try_fold_with(#bind, __folder)?
            }
        })
    });

    s.bound_impl(quote!(::flux_middle::rty::fold::TypeFoldable), quote! {
        fn try_fold_with<__F: ::flux_middle::rty::fold::FallibleTypeFolder>(
            // self,
            &self,
            __folder: &mut __F
        ) -> Result<Self, __F::Error> {
            Ok(match self { #body_fold })
        }
    })
}

pub(crate) fn type_visitable_derive(
    mut s: synstructure::Structure<'_>,
) -> proc_macro2::TokenStream {
    if let syn::Data::Union(_) = s.ast().data {
        panic!("cannot derive on union")
    }

    // if !s.ast().generics.type_params().any(|ty| ty.ident == "I") {
    //     s.add_impl_generic(parse_quote! { I });
    // }

    // s.add_where_predicate(parse_quote! { I: Interner });
    s.add_bounds(synstructure::AddBounds::Fields);
    let body_visit = s.each(|bind| {
        quote! {
            ::flux_middle::rty::fold::TypeVisitable::visit_with(#bind, __visitor)?;
        }
    });
    s.bind_with(|_| synstructure::BindStyle::Move);

    s.bound_impl(quote!(::flux_middle::rty::fold::TypeVisitable), quote! {
        fn visit_with<__V: ::flux_middle::rty::fold::TypeVisitor>(
            &self,
            __visitor: &mut __V
        ) -> ::core::ops::ControlFlow<__V::BreakTy> {
            match *self { #body_visit }
            ::core::ops::ControlFlow::Continue(())
        }
    })
}
