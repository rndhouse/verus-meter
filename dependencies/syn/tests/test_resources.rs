use quote::ToTokens;
use verus_syn::{parse_str, ItemFn};

#[test]
fn resource_clause_survives_clone_and_printing() {
    let function: ItemFn =
        parse_str("fn f(x: bool) requires x, ensures x, resources peak_memory_bytes <= 516, {}")
            .unwrap();
    let copy = function.clone();
    let printed = copy.to_token_stream().to_string();
    let reparsed: ItemFn = parse_str(&printed).unwrap();
    let resources = reparsed.sig.spec.resources.unwrap();
    assert_eq!(resources.resource, "peak_memory_bytes");
    assert_eq!(resources.budget.to_token_stream().to_string(), "516");
    assert!(reparsed.sig.spec.requires.is_some());
    assert!(reparsed.sig.spec.ensures.is_some());
}

#[test]
fn resource_clause_is_erased_for_rust() {
    let mut function: ItemFn = parse_str("fn f() resources peak_memory_bytes <= 0 {}").unwrap();
    function.sig.spec.erase_spec_fields();
    assert!(!function.to_token_stream().to_string().contains("resources"));
}

#[test]
fn malformed_resource_clauses_are_rejected() {
    for text in [
        "fn f() resources heap_bytes <= 8 {}",
        "fn f() resources peak_memory_bytes < 8 {}",
        "fn f() resources peak_memory_bytes <= BUDGET {}",
        "fn f() resources peak_memory_bytes <= -1 {}",
        "fn f() resources peak_memory_bytes <= 18446744073709551616 {}",
        "fn f() resources peak_memory_bytes <= 8u32 {}",
        "fn f() resources peak_memory_bytes <= 4 - 4 {}",
        "fn f() resources peak_local_storage_bytes <= 8 {}",
        "fn f() resources peak_memory_bytes <= memory_budget(x.field) {}",
        "fn f() resources peak_memory_bytes <= memory_budget(make()) {}",
        "fn f() resources peak_memory_bytes <= memory_budget() {}",
        "fn f() resources peak_memory_bytes <= memory_budget::<u32>(x) {}",
        "fn f() resources peak_memory_bytes <= 8 resources peak_memory_bytes <= 9 {}",
    ] {
        assert!(
            parse_str::<ItemFn>(text).is_err(),
            "unexpectedly parsed {text}"
        );
    }
}

#[test]
fn resource_clause_ends_where_clause() {
    let function: ItemFn =
        parse_str("fn f<T>() where T: Copy resources peak_memory_bytes <= 0 {}").unwrap();
    assert!(function.sig.spec.resources.is_some());
}

#[test]
fn expressive_budgets_round_trip() {
    for budget in [
        "4 + 4",
        "memory_budget(x) + memory_budget(module::f)",
        "2 * (memory_budget::<[u32; 8]>() + 4u64)",
    ] {
        let code = format!("fn f(x: u32) resources peak_memory_bytes <= {budget}, {{}}");
        let parsed: ItemFn = parse_str(&code).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}
