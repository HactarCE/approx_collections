#![allow(missing_docs)]

use proc_macro::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    Data, DeriveInput, Error, Field, Fields, GenericParam, Generics, Ident, Index, Meta, Variant,
    parse_macro_input,
};

fn get_impl_block(ident: &Ident, generics: &Generics) -> impl ToTokens {
    let gens2 = generics.params.clone().into_iter().map(|p| match p {
        GenericParam::Lifetime(lifetime_param) => lifetime_param.lifetime.to_token_stream(),
        GenericParam::Type(type_param) => type_param.ident.to_token_stream(),
        GenericParam::Const(const_param) => const_param.ident.to_token_stream(),
    });
    let gens = generics.params.clone().into_iter();
    match &generics.where_clause {
        Some(clause) => {
            quote! {impl<#(#gens ,)*> ::approx_collections::ApproxEq for #ident<#(#gens2 ,)*> #clause}
        }
        None => {
            quote! { impl<#(#gens ,)*> ::approx_collections::ApproxEq for #ident<#(#gens2 ,)*> }
        }
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
        Some(clause) => {
            quote! {impl<#(#gens ,)*> ::approx_collections::ApproxEqZero for #ident<#(#gens2 ,)*> #clause}
        }
        None => {
            quote! { impl<#(#gens ,)*> ::approx_collections::ApproxEqZero for #ident<#(#gens2 ,)*> }
        }
    }
}

fn get_variant_match(variant: &Variant) -> impl ToTokens {
    let ident = &variant.ident;
    match &variant.fields {
        Fields::Named(fields_named) => {
            let fixed_names = fields_named
                .named
                .iter()
                .map(|f| f.ident.as_ref().expect("no field name"));
            let self_names = fixed_names.clone().map(|x| format_ident!("slf_{}", x));
            let other_names = fixed_names.clone().map(|x| format_ident!("other_{}", x));
            let self_names2 = self_names.clone();
            let other_names2 = other_names.clone();
            let fixed_names2 = fixed_names.clone();
            quote! { (Self::#ident{#(#fixed_names: #self_names,)*}, Self::#ident{#(#fixed_names2: #other_names,)*}) => true #(&& ::approx_collections::ApproxEq::approx_eq(&#self_names2, &#other_names2, prec))* }
        }
        Fields::Unnamed(fields_unnamed) => {
            let self_names = (0..fields_unnamed.unnamed.len()).map(|x| format_ident!("slf_{}", x));
            let other_names =
                (0..fields_unnamed.unnamed.len()).map(|x| format_ident!("other_{}", x));
            let self_names2 = self_names.clone();
            let other_names2 = other_names.clone();
            quote! { (Self::#ident(#(#self_names,)*), Self::#ident(#(#other_names,)*)) => true #(&& ::approx_collections::ApproxEq::approx_eq(&#self_names2, &#other_names2, prec))* }
        }
        Fields::Unit => quote! {(Self::#ident, Self::#ident) => true},
    }
}

/// Derives the `ApproxEq` trait on a struct or enum.
///
/// This cannot be used on union types.
///
/// ## Structs
///
/// Two instances of a struct are approximately equal if all of their
/// corresponding fields are approximately equal.
///
/// ```
/// #[derive(Debug, ApproxEq)]
/// struct Coordinate {
///     x: f32,
///     y: f32,
/// }
/// let c1 = Coordinate { x: 5.0, y: 4.0 };
/// let c2 = Coordinate { x: 4.0, y: 5.0 };
/// assert!(ApproxEq::approx_eq(&c1, &c1, Precision::DEFAULT));
/// assert!(!ApproxEq::approx_eq(&c1, &c2, Precision::DEFAULT));
/// ```
///
/// Note that in this example, the `ApproxEq` implementation uses the [taxicab
/// metric] rather than the [Euclidean metric].
///
/// [taxicab metric]: https://en.wikipedia.org/wiki/Taxicab_geometry
/// [Euclidean metric]: https://en.wikipedia.org/wiki/Euclidean_distance
///
/// Tuple structs are also supported.
///
/// ```
/// #[derive(Debug, ApproxEq)]
/// struct Coordinate(f32, f32);
///
/// let c1 = Coordinate(5.0, 4.0);
/// let c2 = Coordinate(4.0, 5.0);
/// assert!(ApproxEq::approx_eq(&c1, &c1, Precision::DEFAULT));
/// assert!(!ApproxEq::approx_eq(&c1, &c2, Precision::DEFAULT));
/// ```
///
/// Two Instances of a unit struct are always approximately equal to each other.
///
/// ## Enums
///
/// Two instances of an enum are approximately equal if they are the same
/// variant and the data they contain is approximately equal.
///
/// Two instances of the same unit variants of an enum are always approximately
/// equal to each other.
///
/// ```
/// #[derive(Debug, ApproxEq)]
/// enum Foo {
///     Bar1 { data: f32 },
///     Bar2(f32),
///     Bar3,
///     Bar4,
/// }
///
/// assert!(ApproxEq::approx_eq(&Foo::Bar1 { data: 5.0 }, &Foo::Bar1 { data: 5.0 }, Precision::DEFAULT));
/// assert!(ApproxEq::approx_eq(&Foo::Bar2(5.0), &Foo::Bar2(5.0), Precision::DEFAULT));
/// assert!(ApproxEq::approx_eq(&Foo::Bar3, &Foo::Bar3, Precision::DEFAULT));
/// assert!(!ApproxEq::approx_eq(&Foo::Bar1 { data: 5.0 }, &Foo::Bar2(5.0), Precision::DEFAULT));
/// assert!(!ApproxEq::approx_eq(&Foo::Bar3, &Foo::Bar4, Precision::DEFAULT));
/// ```
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
                let fixed_names = fields_named
                    .named
                    .iter()
                    .map(|f| f.ident.as_ref().expect("no field name"));
                quote! {
                    #impl_block {
                        fn approx_eq(&self, other: &Self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                            true #(&& ::approx_collections::ApproxEq::approx_eq(&self.#fixed_names, &other.#fixed_names, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unnamed(fields_unnamed) => {
                let i = (0..fields_unnamed.unnamed.len()).map(syn::Index::from);
                quote! {
                    #impl_block {
                        fn approx_eq(&self, other: &Self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                            true #(&& ::approx_collections::ApproxEq::approx_eq(&self.#i, &other.#i, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unit => quote! {
                #impl_block {
                    fn approx_eq(&self, other: &Self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                        true
                    }
                }
            }
            .into(),
        },
        Data::Enum(data_enum) => {
            let match_inner = data_enum.variants.iter().map(get_variant_match);
            quote! {
                #impl_block {
                    fn approx_eq(&self, other: &Self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                        match (self, other) {
                            #(#match_inner,)*
                            _ => false,
                        }
                    }
                }
            }
            .into()
        }
        Data::Union(_) => Error::new(
            Span::mixed_site().into(),
            "derive(ApproxEq) is not implemented for union types.",
        )
        .into_compile_error()
        .into(),
    }
}

/// Derives `ApproxEqZero` on a struct.
///
/// This cannot be used on enums or union types.
///
/// ## Structs
///
/// A struct is approximately equal to zero if all of its fields are
/// approximately equal to zero
///
/// A struct with no fields is always approximately equal to zero.
///
/// ```
/// #[derive(Debug, ApproxEqZero)]
/// struct Coordinate {
///     x: f32,
///     y: f32,
/// }
/// let c1 = Coordinate { x: 0.0, y: 4.0 };
/// let c2 = Coordinate { x: 0.0, y: 0.0 };
/// assert!(!ApproxEqZero::approx_eq_zero(&c1, Precision::DEFAULT));
/// assert!(ApproxEqZero::approx_eq_zero(&c2, Precision::DEFAULT));
/// ```
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
                let fixed_names = fields_named
                    .named
                    .iter()
                    .map(|f| f.ident.as_ref().expect("no field name"));
                quote! {
                    #impl_block {
                        fn approx_eq_zero(&self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                            true #(&& ::approx_collections::ApproxEqZero::approx_eq_zero(&self.#fixed_names, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unnamed(fields_unnamed) => {
                let i = (0..fields_unnamed.unnamed.len()).map(syn::Index::from);
                quote! {
                    #impl_block {
                        fn approx_eq_zero(&self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                            true #(&& ::approx_collections::ApproxEqZero::approx_eq_zero(&self.#i, prec))*
                        }
                    }
                }
                .into()
            }
            Fields::Unit => quote! {
                #impl_block {
                    fn approx_eq_zero(&self, prec: ::approx_collections::Precision) -> ::std::primitive::bool {
                        true
                    }
                }
            }
            .into(),
        },
        Data::Enum(_) => Error::new(
            Span::mixed_site().into(),
            "derive(ApproxEqZero) is not implemented for enum types.",
        )
        .into_compile_error()
        .into(),
        Data::Union(_) => Error::new(
            Span::mixed_site().into(),
            "derive(ApproxEqZero) is not implemented for union types.",
        )
        .into_compile_error()
        .into(),
    }
}

/// Derives the `ApproxInternable` trait.
///
/// This can be used on structs or enums, but not unions.
///
/// When used on a struct, the resulting implementation will call `intern_floats` on every field of the struct.
///
/// When used on an enum, the resulting implementation will call `intern_floats` on every field of the current variant.
///
/// To mark a field as a non float-based field, use the associated marker attribute `#[approx_internable_non_float]`.
///
/// Unit structs and fields need no marker and no floats will be interned.
///
/// ```
/// #[derive(ApproxInternable)]
/// struct Foo {
///     bar1: f64,
///     #[approx_internable_non_float]
///     bar2: u64,
/// }
///
/// #[derive(ApproxInternable)]
/// struct Foo2(f64, #[approx_internable_non_float] u64);
///
/// #[derive(ApproxInternable)]
/// enum Foo3 {
///     Bar1,
///     Bar2(#[approx_internable_non_float] u64, f64),
///     Bar3{x: f64, #[approx_internable_non_float] y: u64},
/// }
/// ```
///
/// Note that you can also use this marker attribute to mark float-based fields you don't want to intern.

#[proc_macro_derive(ApproxInternable, attributes(approx_internable_non_float))]
pub fn derive_approx_internable(input: TokenStream) -> TokenStream {
    fn parse_float_attr(field: &Field) -> bool {
        field.attrs.iter().any(|x| {
            if let Meta::Path(path) = &x.meta
                && path.is_ident("approx_internable_non_float")
            {
                true
            } else {
                false
            }
        })
    }
    fn get_impl_block_internable(ident: &Ident, generics: &Generics) -> impl ToTokens {
        let gens2 = generics.params.clone().into_iter().map(|p| match p {
            GenericParam::Lifetime(lifetime_param) => lifetime_param.lifetime.to_token_stream(),
            GenericParam::Type(type_param) => type_param.ident.to_token_stream(),
            GenericParam::Const(const_param) => const_param.ident.to_token_stream(),
        });
        let gens = generics.params.clone().into_iter();
        match &generics.where_clause {
            Some(clause) => {
                quote! {impl<#(#gens ,)*> ::approx_collections::ApproxInternable for #ident<#(#gens2 ,)*> #clause}
            }
            None => {
                quote! { impl<#(#gens ,)*> ::approx_collections::ApproxInternable for #ident<#(#gens2 ,)*> }
            }
        }
    }

    fn intern_floats_block(data: &Data) -> impl ToTokens {
        fn get_variant_intern_match(var: &Variant) -> impl ToTokens {
            let var_name = &var.ident;
            match &var.fields {
                Fields::Named(fields_named) => {
                    let float_fields = fields_named
                        .named
                        .iter()
                        .filter(|f| !parse_float_attr(f))
                        .map(|x| &x.ident);
                    let all_fields = fields_named.named.iter().map(|x| &x.ident);
                    quote! {Self::#var_name{#(#all_fields,)*} => {#(::approx_collections::ApproxInternable::intern_floats(#float_fields, f);)*},}
                }
                Fields::Unnamed(fields_unnamed) => {
                    let self_names =
                        (0..fields_unnamed.unnamed.len()).map(|x| format_ident!("slf_{}", x));
                    let self_float_names = (0..fields_unnamed.unnamed.len())
                        .filter(|x| !parse_float_attr(fields_unnamed.unnamed.get(*x).unwrap()))
                        .map(|x| format_ident!("slf_{}", x));
                    quote! {Self::#var_name(#(#self_names,)*) => {#(::approx_collections::ApproxInternable::intern_floats(#self_float_names, f);)*},}
                }
                Fields::Unit => quote! {Self::#var_name => {},},
            }
        }
        match data {
            Data::Struct(data_struct) => match &data_struct.fields {
                Fields::Named(fields_named) => {
                    let float_fields = fields_named
                        .named
                        .iter()
                        .filter(|f| !parse_float_attr(f))
                        .map(|x| &x.ident);
                    quote! {
                        fn intern_floats<F: ::std::ops::FnMut(&mut ::std::primitive::f64)>(&mut self, f: &mut F) {
                            #(::approx_collections::ApproxInternable::intern_floats(&mut self.#float_fields, f);)*
                        }
                    }
                }
                Fields::Unnamed(fields_unnamed) => {
                    let float_nums = (0..fields_unnamed.unnamed.len())
                        .filter(|i| !parse_float_attr(fields_unnamed.unnamed.get(*i).unwrap()))
                        .map(Index::from);
                    quote! {
                        fn intern_floats<F: ::std::ops::FnMut(&mut ::std::primitive::f64)>(&mut self, f: &mut F) {
                            #(::approx_collections::ApproxInternable::intern_floats(&mut self.#float_nums, f);)*
                        }
                    }
                }
                Fields::Unit => quote! {
                    fn intern_floats<F: ::std::ops::FnMut(&mut ::std::primitive::f64)>(&mut self, f: &mut F) {}
                },
            },
            Data::Enum(data_enum) => {
                let match_vars = data_enum
                    .variants
                    .iter()
                    .map(|x| get_variant_intern_match(x));
                quote! {
                    fn intern_floats<F: ::std::ops::FnMut(&mut ::std::primitive::f64)>(&mut self, f: &mut F) {
                            match self {#(#match_vars)*}
                    }
                }
            }

            Data::Union(_) => Error::new(
                Span::mixed_site().into(),
                "derive(ApproxEqZero) is not implemented for union types.",
            )
            .into_compile_error()
            .into(),
        }
    }
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = parse_macro_input!(input);
    let impl_block = get_impl_block_internable(&ident, &generics);
    let intern_floats = intern_floats_block(&data);
    quote! {
        #impl_block {
            #intern_floats
        }
    }
    .into()
}
