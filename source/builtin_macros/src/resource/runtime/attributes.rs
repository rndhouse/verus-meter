//! Keep query declarations under the function's configuration without copying
//! function-only attributes onto modules. Conditional query markers are rejected
//! explicitly; helper variants cannot be selected before rustc evaluates cfgs.
use verus_syn::punctuated::Punctuated;
use verus_syn::{Attribute, Meta, Token};

pub(super) fn requested(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attribute| contains_query(&attribute.meta))
}

fn contains_query(meta: &Meta) -> bool {
    if meta.path().is_ident("queryable_peak_memory") {
        return true;
    }
    let Meta::List(list) = meta else { return false };
    list.path.is_ident("cfg_attr")
        && list
            .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
            .is_ok_and(|nested| nested.iter().skip(1).any(contains_query))
}

pub(super) fn take(attributes: &mut Vec<Attribute>) -> Option<verus_syn::Result<()>> {
    let requests: Vec<_> = attributes.iter().filter(|a| contains_query(&a.meta)).cloned().collect();
    if requests.is_empty() {
        return None;
    }
    attributes.retain(|a| !contains_query(&a.meta));
    if requests.iter().any(|a| !a.path().is_ident("queryable_peak_memory")) {
        return Some(Err(verus_syn::Error::new_spanned(
            &requests[0],
            "place #[queryable_peak_memory] directly on the function; use #[cfg] to gate the function",
        )));
    }
    Some(if requests.len() != 1 || !matches!(requests[0].meta, Meta::Path(_)) {
        Err(verus_syn::Error::new_spanned(
            &requests[0],
            "expected one #[queryable_peak_memory] attribute",
        ))
    } else {
        Ok(())
    })
}

pub(super) fn configuration(attributes: &[Attribute]) -> Vec<Attribute> {
    selected(attributes, configuration_meta)
}

/// Carry source allowances to generated code, while checking lint expectations
/// only on the original function. Stricter policies still check that function.
pub(super) fn allowances(attributes: &[Attribute]) -> Vec<Attribute> {
    selected(attributes, allowance_meta)
}

fn selected(attributes: &[Attribute], select: fn(&Meta) -> Option<Meta>) -> Vec<Attribute> {
    attributes
        .iter()
        .filter_map(|attribute| {
            let mut attribute = attribute.clone();
            attribute.meta = select(&attribute.meta)?;
            Some(attribute)
        })
        .collect()
}

fn configuration_meta(meta: &Meta) -> Option<Meta> {
    // Like upstream ghost stubs, query modules follow test-only item removal
    // without becoming tests themselves.
    if meta.path().is_ident("test") {
        return Some(verus_syn::parse_quote!(cfg(test)));
    }
    if meta.path().is_ident("cfg") {
        return Some(meta.clone());
    }
    conditional(meta, configuration_meta)
}

fn allowance_meta(meta: &Meta) -> Option<Meta> {
    if meta.path().is_ident("allow") || meta.path().is_ident("warn") {
        return Some(meta.clone());
    }
    if let Meta::List(list) = meta {
        if list.path.is_ident("expect") {
            let tokens = &list.tokens;
            return Some(verus_syn::parse_quote!(allow(#tokens)));
        }
    }
    conditional(meta, allowance_meta)
}

fn conditional(meta: &Meta, select: fn(&Meta) -> Option<Meta>) -> Option<Meta> {
    let Meta::List(list) = meta else { return None };
    if !list.path.is_ident("cfg_attr") {
        return None;
    }
    let nested = list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated).ok()?;
    let condition = nested.first()?;
    let configuration: Vec<_> = nested.iter().skip(1).filter_map(select).collect();
    if configuration.is_empty() {
        return None;
    }
    Some(verus_syn::parse_quote!(cfg_attr(#condition, #(#configuration),*)))
}
