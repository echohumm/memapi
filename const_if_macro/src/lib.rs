use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse_macro_input,
    ItemFn,
    Meta,
    token::Const
};

#[proc_macro_attribute]
pub fn const_if(attr: TokenStream, item: TokenStream) -> TokenStream {
    // parse the incoming attribute tokens
    let cfg_meta: Meta = parse_macro_input!(attr as Meta);

    // parse the function itself
    let original: ItemFn = parse_macro_input!(item as ItemFn);

    // build the `const fn`
    let mut const_version = original.clone();
    // turn `fn foo(...)` into `const fn foo(...)`
    const_version.sig.constness = Some(Const::default());
    // add `#[cfg(cfg_meta)]`
    const_version
        .attrs
        .push(syn::parse_quote!(#[cfg(#cfg_meta)]));

    // build the non-const version
    let mut non_const_version = original;
    // negate the cfg
    non_const_version
        .attrs
        .push(syn::parse_quote!(#[cfg(not(#cfg_meta))]));

    // emit both
    TokenStream::from(quote! {
        #const_version
        #non_const_version
    })
}
