//! Emit typed constants for runtime memory-size queries. Rust resolves aliases
//! and type identity; shared source-model traits supply bytes without ABI sizing.
use proc_macro2::TokenStream;
use quote::quote;
use verus_syn::{Ident, Type};

pub(in crate::syntax::resource) fn size(name: &Ident, ty: &Type) -> TokenStream {
    let bytes = if name == "value_size" {
        quote!(<#ty as ::verus_meter_runtime::ValueSize>::BYTES)
    } else if name == "for_loop_size" {
        quote!(<#ty as ::verus_meter_runtime::ForLoopSize>::BYTES)
    } else {
        quote!(<#ty as ::verus_meter_runtime::ReferenceSize>::BYTES)
    };
    quote!(::verus_meter_runtime::Expression::constant(#bytes))
}
