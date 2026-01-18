#![allow(missing_docs)]

use proc_macro::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Data, DeriveInput, Fields, GenericParam, Generics, Ident, TypeParam, Variant, parse_macro_input,
};

fn get_impl_block(ident: &Ident, generics: &Generics) -> impl ToTokens {
    let gens2 = generics.params.clone().into_iter().map(|p| match p {
        GenericParam::Lifetime(lifetime_param) => lifetime_param.lifetime.to_token_stream(),
        GenericParam::Type(type_param) => type_param.ident.to_token_stream(),
        GenericParam::Const(const_param) => const_param.ident.to_token_stream(),
    });
    let gens = generics.params.clone().into_iter();
    match &generics.where_clause {
        Some(clause) => quote! {impl<#(#gens ,)*> ApproxEq for #ident<#(#gens2 ,)*> #clause},
        None => quote! { impl<#(#gens ,)*> ApproxEq for #ident<#(#gens2 ,)*> },
    }
}

fn get_impl_block_zero(ident: &Ident, generics: &Generics) -> impl ToTokens {
    let gens2 = generics.params.clone().into_iter().map(|p| match p {
        GenericParam::Lifetime(lifetime_param) => lifetime_param.lifetime.to_token_stream(),
        GenericParam::Type(type_param) => type_param.ident.to_token_stream(),
        GenericParam::Const(const_param) => const_param.ident.to_token_stream(),
    });
    let gens = generics.params.clone().into_iter();
    match &generics.where_clause {
        Some(clause) => quote! {impl<#(#gens ,)*> ApproxEqZero for #ident<#(#gens2 ,)*> #clause},
        None => quote! { impl<#(#gens ,)*> ApproxEqZero for #ident<#(#gens2 ,)*> },
    }
}

fn get_variant_match(variant: &Variant) -> impl ToTokens {
    let ident = &variant.ident;
    match &variant.fields {
        Fields::Named(fields_named) => {
            let fixed_names = fields_named.named.iter().map(|f| f.ident.as_ref().unwrap());
            let self_names = fixed_names.clone().map(|x| format_ident!("slf_{}", x));
            let other_names = fixed_names.clone().map(|x| format_ident!("other_{}", x));
            let self_names2 = self_names.clone();
            let other_names2 = other_names.clone();
            let fixed_names2 = fixed_names.clone();
            quote! { (Self::#ident{#(#fixed_names: #self_names,)*}, Self::#ident{#(#fixed_names2: #other_names,)*}) => true #(&& ApproxEq::approx_eq(&#self_names2, &#other_names2, prec))* }
        }
        Fields::Unnamed(fields_unnamed) => {
            let self_names = (0..fields_unnamed.unnamed.len()).map(|x| format_ident!("slf_{}", x));
            let other_names =
                (0..fields_unnamed.unnamed.len()).map(|x| format_ident!("other_{}", x));
            let self_names2 = self_names.clone();
            let other_names2 = other_names.clone();
            quote! { (Self::#ident(#(#self_names,)*), Self::#ident(#(#other_names,)*)) => true #(&& ApproxEq::approx_eq(&#self_names2, &#other_names2, prec))* }
        }
        Fields::Unit => quote! {(Self::#ident, Self::#ident) => true},
    }
}

#[proc_macro_derive(ApproxEq)]
pub fn derive_approx_eq(input: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = parse_macro_input!(input);
    let impl_block = get_impl_block(&ident, &generics);
    match data {
        Data::Struct(data_struct) => match data_struct.fields {
            Fields::Named(fields_named) => {
                let fixed_names = fields_named.named.iter().map(|f| f.ident.as_ref().unwrap());
                quote! {
                    #impl_block {
                        fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
                            true #(&& ApproxEq::approx_eq(&self.#fixed_names, &other.#fixed_names, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unnamed(fields_unnamed) => {
                let i = (0..fields_unnamed.unnamed.len()).map(syn::Index::from);
                quote! {
                    #impl_block {
                        fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
                            true #(&& ApproxEq::approx_eq(&self.#i, &other.#i, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unit => quote! {
                #impl_block {
                    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
                        true
                    }
                }
            }
            .into(),
        },
        Data::Enum(data_enum) => {
            let match_inner = data_enum.variants.iter().map(|x| get_variant_match(x));
            quote! {
                #impl_block {
                    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
                        match (self, other) {
                            #(#match_inner,)*
                            _ => false,
                        }
                    }
                }
            }
            .into()
        }
        Data::Union(_) => panic!("derive(ApproxEq) is not implemented for union types!"),
    }
}

#[proc_macro_derive(ApproxEqZero)]
pub fn derive_approx_eq_zero(input: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = parse_macro_input!(input);
    let impl_block = get_impl_block_zero(&ident, &generics);
    match data {
        Data::Struct(data_struct) => match data_struct.fields {
            Fields::Named(fields_named) => {
                let fixed_names = fields_named.named.iter().map(|f| f.ident.as_ref().unwrap());
                quote! {
                    #impl_block {
                        fn approx_eq_zero(&self, prec: Precision) -> bool {
                            true #(&& ApproxEqZero::approx_eq_zero(&self.#fixed_names, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unnamed(fields_unnamed) => {
                let i = (0..fields_unnamed.unnamed.len()).map(syn::Index::from);
                quote! {
                    #impl_block {
                        fn approx_eq_zero(&self, prec: Precision) -> bool {
                            true #(&& ApproxEqZero::approx_eq_zero(&self.#i, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unit => quote! {
                #impl_block {
                    fn approx_eq_zero(&self, prec: Precision) -> bool {
                        true
                    }
                }
            }
            .into(),
        },
        Data::Enum(_) => panic!("derive(ApproxEqZero) is not implemented for enum types."),
        Data::Union(_) => panic!("derive(ApproxEqZero) is not implemented for union types."),
    }
}
