//! Extract expression data before ordinary signature lowering and erasure.
mod attributes;
mod extract;

use extract::{Binding, Extractor, Kind};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use verus_syn::ext::IdentExt;
use verus_syn::{FnArgKind, FnMode, ImplItem, Item, ItemFn, Pat, TraitItem, Type};

pub(in crate::syntax) fn expand(items: &mut Vec<Item>) {
    let mut generated = Vec::new();
    for item in items.iter_mut() {
        let non_function = match item {
            Item::Struct(item) => Some(&mut item.attrs),
            Item::Enum(item) => Some(&mut item.attrs),
            Item::Union(item) => Some(&mut item.attrs),
            Item::Type(item) => Some(&mut item.attrs),
            Item::Const(item) => Some(&mut item.attrs),
            Item::Static(item) => Some(&mut item.attrs),
            Item::Mod(item) => Some(&mut item.attrs),
            Item::Trait(item) => Some(&mut item.attrs),
            Item::Impl(item) => Some(&mut item.attrs),
            _ => None,
        };
        if let Some(attributes) = non_function {
            let cfg = attributes::configuration(attributes);
            if attributes::take(attributes).is_some() {
                generated.push(Item::Verbatim(quote!(#(#cfg)* ::core::compile_error!("place queryable_peak_memory on a free function, not this item");)));
            }
        }
        let (outer, members): (_, Vec<_>) = match item {
            Item::Impl(implementation) => (
                &implementation.attrs,
                implementation
                    .items
                    .iter_mut()
                    .filter_map(|item| match item {
                        ImplItem::Fn(method) => Some(&mut method.attrs),
                        _ => None,
                    })
                    .collect(),
            ),
            Item::Trait(definition) => (
                &definition.attrs,
                definition
                    .items
                    .iter_mut()
                    .filter_map(|item| match item {
                        TraitItem::Fn(method) => Some(&mut method.attrs),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => continue,
        };
        for member in members {
            let cfg = attributes::configuration(member);
            if attributes::take(member).is_some() {
                let outer = attributes::configuration(outer);
                generated.push(Item::Verbatim(quote!(#(#outer)* #(#cfg)* ::core::compile_error!("queryable_peak_memory supports free functions only, not methods");)));
            }
        }
    }
    // Most blocks have no query requests. Avoid cloning their spec/function ASTs.
    if !items
        .iter()
        .any(|item| matches!(item, Item::Fn(function) if attributes::requested(&function.attrs)))
    {
        items.extend(generated);
        return;
    }
    let functions: HashMap<_, _> = items
        .iter()
        .filter_map(|item| match item {
            Item::Fn(f) => Some((f.sig.ident.unraw().to_string(), f.clone())),
            _ => None,
        })
        .collect();
    let occupied: Vec<_> = items
        .iter()
        .filter_map(|item| match item {
            Item::Mod(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            Item::Struct(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            Item::Enum(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            Item::Union(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            Item::Type(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            Item::Trait(item) if attributes::configuration(&item.attrs).is_empty() => {
                Some(item.ident.unraw())
            }
            _ => None,
        })
        .collect();
    for item in items.iter_mut() {
        let Item::Fn(function) = item else { continue };
        let cfg = attributes::configuration(&function.attrs);
        let Some(request) = attributes::take(&mut function.attrs) else { continue };
        let result = request.and_then(|()| {
            if occupied.contains(&function.sig.ident.unraw()) {
                return Err(verus_syn::Error::new_spanned(&function.sig.ident, "query namespace is already occupied by a type or module; rename that item or the function"));
            }
            query(function, &functions)
        });
        let tokens = result.unwrap_or_else(|e| {
            let error = e.to_compile_error();
            quote!(#(#cfg)* #error)
        });
        generated.push(Item::Verbatim(tokens));
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
        || sig.constness.is_some()
        || sig.variadic.is_some()
        || crate::syntax::has_external_code(&function.attrs)
        || function.semi_token.is_some()
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
        environment
            .insert(name.unraw().to_string(), Binding::parameter(kind, (**ty).clone(), index));
        parameters.push(quote!(#name: #ty));
        inputs.push(quote!(::verus_meter_runtime::Input::from(#name)));
    }
    let contract = sig.spec.resources.as_ref().ok_or_else(|| {
        verus_syn::Error::new_spanned(
            &sig.ident,
            "queryable_peak_memory requires resources peak(memory) <= bound",
        )
    })?;
    let mut extractor = Extractor::new(functions);
    let expression = extractor.budget(&contract.budget, &environment)?;
    let nodes = extractor.nodes();
    let name = &sig.ident;
    let visibility = &function.vis;
    let documentation = format!("Runtime resource queries for the `{name}` function.");
    let allowances = attributes::allowances(&function.attrs);
    let cfg = attributes::configuration(&function.attrs);
    // Keep the marker distinct from the function module imported by super::*.
    let marker = if name.unraw() == "QueryData" { "QueryDataStorage" } else { "QueryData" };
    let data = verus_syn::Ident::new(marker, proc_macro2::Span::mixed_site());
    Ok(quote! {
        #(#cfg)*
        #[verifier::external]
        #[doc = #documentation]
        #(#allowances)*
        #visibility mod #name {
            // The parent-scope implementation owns the expression constants.
            pub(super) enum #data {}

            // Preserve aliases used by the source parameter types.
            use super::*;
            // Keep the namespace import used even for formulas containing no
            // named types, without overriding a caller's unused-import policy.
            const _: () = { let _ = #name::peak_memory_bound; };
            /// Evaluate the declared allowance. Execution preconditions remain the caller's responsibility.
            pub fn peak_memory_bound(#(#parameters),*) -> ::core::result::Result<::verus_meter_runtime::ModelBytes, ::verus_meter_runtime::QueryError> {
                ::verus_meter_runtime::evaluate_program(&#data::PROGRAM, &[#(#inputs),*])
            }
        }

        // An impl does not introduce a module scope. Resolve every source type
        // and array-length path here, where self/super have their original meaning.
        #(#cfg)*
        #[verifier::external]
        impl #name::#data {
            const PROGRAM: ::verus_meter_runtime::Program =
                ::verus_meter_runtime::Program::new(#expression, &[#(#nodes),*]);
        }
    })
}

#[cfg(test)]
mod tests;
