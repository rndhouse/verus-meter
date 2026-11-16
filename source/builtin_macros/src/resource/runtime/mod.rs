//! Retain resource formulas before the normal visitor erases signature specs.
//!
//! Both compiler passes expand the same parsed declaration into expression data.
//! No artifact is handed between passes. This prototype only needs syntax-level
//! quantities; typed sizes and spec helpers require later integration.

use proc_macro2::TokenStream;
use quote::quote;
use verus_syn::{FnArgKind, FnMode, Item, ItemFn, Pat, ResourceExpr, Type};

pub(in crate::syntax) fn expand(items: &mut Vec<Item>) {
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
                query(function)
            };
        generated.push(Item::Verbatim(result.unwrap_or_else(|e| e.to_compile_error())));
    }
    items.extend(generated);
}

fn query(function: &ItemFn) -> verus_syn::Result<TokenStream> {
    let signature = &function.sig;
    let unsupported = || {
        verus_syn::Error::new_spanned(
            &signature.ident,
            "queryable peak memory currently requires a safe nongeneric exec free function with one unsigned scalar parameter",
        )
    };
    if !matches!(signature.mode, FnMode::Default | FnMode::Exec(_))
        || signature.unsafety.is_some()
        || signature.asyncness.is_some()
        || signature.abi.is_some()
        || !signature.generics.params.is_empty()
        || signature.generics.where_clause.is_some()
        || signature.inputs.len() != 1
    {
        return Err(unsupported());
    }
    let argument = signature.inputs.first().ok_or_else(unsupported)?;
    if argument.tracked.is_some() {
        return Err(unsupported());
    }
    let FnArgKind::Typed(argument) = &argument.kind else { return Err(unsupported()) };
    let Pat::Ident(parameter) = &*argument.pat else { return Err(unsupported()) };
    let Type::Path(typ) = &*argument.ty else { return Err(unsupported()) };
    if parameter.by_ref.is_some()
        || parameter.mutability.is_some()
        || parameter.subpat.is_some()
        || typ.qself.is_some()
        || !typ.path.get_ident().is_some_and(|i| {
            matches!(i.to_string().as_str(), "u8" | "u16" | "u32" | "u64" | "usize")
        })
    {
        return Err(unsupported());
    }
    let contract = signature.spec.resources.as_ref().ok_or_else(|| {
        verus_syn::Error::new_spanned(
            &signature.ident,
            "queryable_peak_memory requires resources peak(memory) <= bound",
        )
    })?;
    let expression = retain(&contract.budget, &parameter.ident)?;
    let name = &signature.ident;
    let visibility = &function.vis;
    let ty = &argument.ty;
    // External module: query tooling is tested Rust, outside target verification.
    // Verbatim output prevents the visitor from rewriting native arithmetic/types.
    Ok(quote! {
        #[verifier::external]
        #visibility mod #name {
            /// Evaluate the declared peak-memory allowance in model bytes.
            /// The caller remains responsible for execution preconditions.
            pub fn peak_memory_bound(input: #ty) -> ::core::result::Result<::verus_meter_runtime::ModelBytes, ::verus_meter_runtime::QueryError> {
                static EXPRESSION: ::verus_meter_runtime::Expression = #expression;
                ::verus_meter_runtime::evaluate(&EXPRESSION, &[::verus_meter_runtime::Input::from(input)])
            }
        }
    })
}

fn retain(
    expression: &ResourceExpr,
    parameter: &verus_syn::Ident,
) -> verus_syn::Result<TokenStream> {
    let constructor = quote!(::verus_meter_runtime::Expression);
    Ok(match expression {
        ResourceExpr::Literal(value) => quote!(#constructor::constant(#value)),
        ResourceExpr::Quantity(name) if name == parameter => quote!(#constructor::parameter(0)),
        ResourceExpr::Paren(_, inner) => retain(inner, parameter)?,
        ResourceExpr::Add(left, _, right) | ResourceExpr::Mul(left, _, right) => {
            let left = retain(left, parameter)?;
            let right = retain(right, parameter)?;
            if matches!(expression, ResourceExpr::Add(..)) {
                quote!(#constructor::add(&#left, &#right))
            } else {
                quote!(#constructor::multiply(&#left, &#right))
            }
        }
        _ => {
            return Err(verus_syn::Error::new_spanned(
                expression,
                "queryable peak memory currently supports constants, its unsigned parameter, addition, and multiplication",
            ));
        }
    })
}
