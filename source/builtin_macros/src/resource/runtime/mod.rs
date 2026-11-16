//! Extract expression data before ordinary signature lowering and erasure.
mod extract;

use extract::{Binding, Extractor, Kind};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use verus_syn::{FnArgKind, FnMode, Item, ItemFn, Pat, Type};

pub(in crate::syntax) fn expand(items: &mut Vec<Item>) {
    // Most blocks have no query requests. Avoid cloning their spec/function ASTs.
    if !items.iter().any(|item| matches!(item, Item::Fn(function) if function.attrs.iter().any(|a| a.path().is_ident("queryable_peak_memory")))) {
        return;
    }
    let functions: HashMap<_, _> = items
        .iter()
        .filter_map(|item| match item {
            Item::Fn(f) => Some((f.sig.ident.to_string(), f.clone())),
            _ => None,
        })
        .collect();
    let mut generated = Vec::new();
    for item in items.iter_mut() {
        let Item::Fn(function) = item else { continue };
        let attributes: Vec<_> = function
            .attrs
            .iter()
            .filter(|a| a.path().is_ident("queryable_peak_memory"))
            .cloned()
            .collect();
        if attributes.is_empty() {
            continue;
        }
        function.attrs.retain(|a| !a.path().is_ident("queryable_peak_memory"));
        let result =
            if attributes.len() != 1 || !matches!(attributes[0].meta, verus_syn::Meta::Path(_)) {
                Err(verus_syn::Error::new_spanned(
                    &attributes[0],
                    "expected one #[queryable_peak_memory] attribute",
                ))
            } else {
                query(function, &functions)
            };
        generated.push(Item::Verbatim(result.unwrap_or_else(|e| e.to_compile_error())));
    }
    items.extend(generated);
}

fn query(function: &ItemFn, functions: &HashMap<String, ItemFn>) -> verus_syn::Result<TokenStream> {
    let sig = &function.sig;
    let unsupported = || {
        verus_syn::Error::new_spanned(
            &sig.ident,
            "queryable peak memory requires a safe nongeneric exec free function with unsigned scalar or Boolean parameters",
        )
    };
    if !matches!(sig.mode, FnMode::Default | FnMode::Exec(_))
        || sig.unsafety.is_some()
        || sig.asyncness.is_some()
        || sig.abi.is_some()
        || !sig.generics.params.is_empty()
        || sig.generics.where_clause.is_some()
    {
        return Err(unsupported());
    }
    let mut environment = HashMap::new();
    let mut parameters = Vec::new();
    let mut inputs = Vec::new();
    for (index, argument) in sig.inputs.iter().enumerate() {
        if argument.tracked.is_some() {
            return Err(unsupported());
        }
        let FnArgKind::Typed(argument) = &argument.kind else { return Err(unsupported()) };
        let Pat::Ident(parameter) = &*argument.pat else { return Err(unsupported()) };
        let Type::Path(path) = &*argument.ty else { return Err(unsupported()) };
        let kind = match path.path.get_ident().map(ToString::to_string).as_deref() {
            Some("u8" | "u16" | "u32" | "u64" | "usize") => Kind::Integer,
            Some("bool") => Kind::Boolean,
            _ => return Err(unsupported()),
        };
        if parameter.by_ref.is_some()
            || parameter.mutability.is_some()
            || parameter.subpat.is_some()
            || path.qself.is_some()
        {
            return Err(unsupported());
        }
        let name = &parameter.ident;
        let ty = &argument.ty;
        let constructor = kind.constructor();
        environment.insert(
            name.to_string(),
            Binding {
                tokens: quote!(#constructor::parameter(#index)),
                kind,
                ty: Some((**ty).clone()),
            },
        );
        parameters.push(quote!(#name: #ty));
        inputs.push(quote!(::verus_meter_runtime::Input::from(#name)));
    }
    let contract = sig.spec.resources.as_ref().ok_or_else(|| {
        verus_syn::Error::new_spanned(
            &sig.ident,
            "queryable_peak_memory requires resources peak(memory) <= bound",
        )
    })?;
    let expression = Extractor::new(functions).budget(&contract.budget, &environment)?;
    let name = &sig.ident;
    let visibility = &function.vis;
    let data = verus_syn::Ident::new("__VERUS_QUERY_EXPRESSION", proc_macro2::Span::mixed_site());
    Ok(quote! {
        #[verifier::external]
        #visibility mod #name {
            // Size types may be aliases in the surrounding module.
            #[allow(unused_imports)]
            use super::*;
            /// Evaluate the declared allowance. Execution preconditions remain the caller's responsibility.
            pub fn peak_memory_bound(#(#parameters),*) -> ::core::result::Result<::verus_meter_runtime::ModelBytes, ::verus_meter_runtime::QueryError> {
                static #data: ::verus_meter_runtime::Expression = #expression;
                ::verus_meter_runtime::evaluate(&#data, &[#(#inputs),*])
            }
        }
    })
}
