use verus_prettyplease as prettyplease;
use verus_syn as syn;

use indoc::indoc;
use proc_macro2::{Delimiter, Group, TokenStream};
use quote::quote;

#[track_caller]
fn test(tokens: TokenStream, expected: &str) {
    let syntax_tree: syn::File = syn::parse2(tokens).unwrap();
    let pretty = prettyplease::unparse(&syntax_tree);
    assert_eq!(pretty, expected);
}

#[test]
fn test_parenthesize_cond() {
    let s = Group::new(Delimiter::None, quote!(Struct {}));
    test(
        quote! {
            fn main() {
                if #s == #s {}
            }
        },
        indoc! {"
            fn main() {
                if (Struct {}) == (Struct {}) {}
            }
        "},
    );
}

#[test]
fn test_parenthesize_match_guard() {
    let expr_struct = Group::new(Delimiter::None, quote!(Struct {}));
    let expr_binary = Group::new(Delimiter::None, quote!(true && false));
    test(
        quote! {
            fn main() {
                match () {
                    () if let _ = #expr_struct => {}
                    () if let _ = #expr_binary => {}
                }
            }
        },
        indoc! {"
            fn main() {
                match () {
                    () if let _ = Struct {} => {}
                    () if let _ = (true && false) => {}
                }
            }
        "},
    );
}

#[test]
fn spec_budget_calls_round_trip() {
    let parsed: syn::Expr =
        syn::parse_str("mem_peak <= mem_size(n) + budgets::bytes(n as nat) {}").unwrap();
    let printed = prettyplease::unparse_expr(&parsed);
    let reparsed: syn::Expr = syn::parse_str(&printed).unwrap();
    assert_eq!(quote!(#parsed).to_string(), quote!(#reparsed).to_string());
}

#[test]
fn memory_query_type_round_trip() {
    let parsed: syn::Expr = syn::parse_str("mem_size(Vec<u32>)").unwrap();
    let printed = prettyplease::unparse_expr(&parsed);
    let reparsed: syn::Expr = syn::parse_str(&printed).unwrap();
    assert_eq!(quote!(#parsed).to_string(), quote!(#reparsed).to_string());
}
