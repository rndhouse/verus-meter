use quote::quote;
use verus_prettyplease as prettyplease;
use verus_syn as syn;

#[test]
fn memory_checkpoints_are_omitted_without_losing_executable_statements() {
    // This printer deliberately omits proof statements from documentation.
    // Memory checkpoints follow that policy; surrounding executable code stays.
    let file = syn::parse_file(
        "fn f() resources peak(memory) <= 128 {
            let local = 7u32;
            #[allow(unused)] assert(peak(memory) <= value_size(local) + peak(helper));
            assert(current(memory) <= 0,);
            consume(local);
        }",
    )
    .unwrap();
    let printed = prettyplease::unparse(&file);
    let reparsed = syn::parse_file(&printed).unwrap();
    let expected = syn::parse_file(
        "fn f() resources peak(memory) <= 128 { let local = 7u32; consume(local); }",
    )
    .unwrap();
    assert_eq!(quote!(#expected).to_string(), quote!(#reparsed).to_string());
}

#[test]
fn spec_budget_calls_round_trip() {
    let parsed: syn::Expr =
        syn::parse_str("resources peak(memory) <= value_size(n) + budgets::bytes(n as nat) {}")
            .unwrap();
    let printed = prettyplease::unparse_expr(&parsed);
    let reparsed: syn::Expr = syn::parse_str(&printed).unwrap();
    assert_eq!(quote!(#parsed).to_string(), quote!(#reparsed).to_string());
}

#[test]
fn memory_query_type_round_trip() {
    for query in ["value_size(Box<[u32; 4]>)", "ref_size(&mut [u32])"] {
        let parsed: syn::Expr = syn::parse_str(query).unwrap();
        let printed = prettyplease::unparse_expr(&parsed);
        let reparsed: syn::Expr = syn::parse_str(&printed).unwrap();
        assert_eq!(quote!(#parsed).to_string(), quote!(#reparsed).to_string());
    }
}

#[test]
fn argument_specific_budget_round_trip() {
    let file = verus_syn::parse_file(
        "fn f(flag: bool) { resources peak(memory) <= value_size(flag) + peak(module::helper(!flag, 4u32,)) + return_size(module::helper) { resources peak(memory) <= peak(helper(false)) {} } }",
    ).unwrap();
    let pretty = prettyplease::unparse(&file);
    let reparsed = verus_syn::parse_file(&pretty).unwrap();
    assert_eq!(quote!(#file).to_string(), quote!(#reparsed).to_string());
}

#[test]
fn conditional_budget_round_trip() {
    let file = verus_syn::parse_file(
        "fn f() { resources peak(memory) <= value_size(flag) + if flag { 32 } else { 16 } { let x = 1; } }",
    )
    .unwrap();
    let pretty = prettyplease::unparse(&file);
    let reparsed = verus_syn::parse_file(&pretty).unwrap();
    assert_eq!(quote!(#file).to_string(), quote!(#reparsed).to_string());
}

#[test]
fn memory_sections_keep_executable_contents() {
    let file = verus_syn::parse_file(
        "fn f() { resources peak(memory) <= 2 * (value_size([u32; 4]) + peak(helper)) { let x = 1; resources peak(memory) <= 0 { consume(x); } } }",
    ).unwrap();
    let pretty = prettyplease::unparse(&file);
    let reparsed = verus_syn::parse_file(&pretty).unwrap();
    assert_eq!(quote!(#file).to_string(), quote!(#reparsed).to_string());
}
