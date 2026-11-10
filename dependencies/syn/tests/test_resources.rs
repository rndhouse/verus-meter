use quote::ToTokens;
use verus_syn::{parse_str, ItemFn};

#[test]
fn resource_clause_survives_clone_and_printing() {
    let function: ItemFn =
        parse_str("fn f(x: bool) requires x, ensures x, resources peak(memory) <= 516, {}")
            .unwrap();
    let copy = function.clone();
    let printed = copy.to_token_stream().to_string();
    let reparsed: ItemFn = parse_str(&printed).unwrap();
    let resources = reparsed.sig.spec.resources.unwrap();
    assert!(resources.resources_token.is_some());
    assert!(resources.peak.is_some());
    assert_eq!(resources.token.to_token_stream().to_string(), "memory");
    assert_eq!(resources.budget.to_token_stream().to_string(), "516");
    assert!(reparsed.sig.spec.requires.is_some());
    assert!(reparsed.sig.spec.ensures.is_some());
}

#[test]
fn resource_clause_is_erased_for_rust() {
    let mut function: ItemFn = parse_str("fn f() resources peak(memory) <= 0 {}").unwrap();
    function.sig.spec.erase_spec_fields();
    assert!(!function.to_token_stream().to_string().contains("peak"));
}

#[test]
fn malformed_resource_clauses_are_rejected() {
    for text in [
        "fn f() resources heap_bytes <= 8 {}",
        "fn f() peak <= 8 {}",
        "fn f() resources peak <= 8 {}",
        "fn f() resources peak memory <= 8 {}",
        "fn f() resources peak() <= 8 {}",
        "fn f() resources peak(other) <= 8 {}",
        "fn f() resources peak(memory, memory) <= 8 {}",
        "fn f() resources current(memory) <= 8 {}",
        "fn f() resources {}",
        "fn f() resources work <= 8 {}",
        "fn f() resources peak(memory) <= 8, peak <= 9 {}",
        "fn f() resources peak(memory) < 8 {}",
        "fn f() resources peak(memory) <= -1 {}",
        "fn f() resources peak(memory) <= 18446744073709551616 {}",
        "fn f() resources peak(memory) <= 8u32 {}",
        "fn f() resources peak(memory) <= 4 - 4 {}",
        "fn f() resources peak(memory) <= peak(x.field) {}",
        "fn f() resources peak(memory) <= peak(object.make()) {}",
        "fn f() resources peak(memory) <= peak() {}",
        "fn f() resources peak(memory) <= value_size() {}",
        "fn f() resources peak(memory) <= value_size(x.field) {}",
        "fn f() resources peak(memory) <= value_size(make()) {}",
        "fn f() resources peak(memory) <= value_size(4) {}",
        "fn f() resources peak(memory) <= value_size(x, y) {}",
        "fn f() resources peak(memory) <= peak(x, y) {}",
        "fn f() resources peak(memory) <= peak([u32; 4]) {}",
        "fn f() resources peak(memory) <= 8 resources peak(memory) <= 9 {}",
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
        parse_str("fn f<T>() where T: Copy resources peak(memory) <= 0 {}").unwrap();
    assert!(function.sig.spec.resources.is_some());
}

#[test]
fn expressive_budgets_round_trip() {
    for budget in [
        "BUDGET",
        "budgets::workspace(flag, n as nat)",
        "budgets::formula(4)(n as nat)",
        "value_size(n) + workspace(n) * 2",
        "workspace::<u32>()",
        "value_size(n) + n * value_size(u32)",
        "4 + 4",
        "value_size(x) + peak(module::f)",
        "2 * (value_size([u32; 8]) + 4u64)",
        "value_size(crate::Buffer) + value_size(&mut [u32]) + value_size(())",
        "value_size([[u32; 4]; 2]) + value_size(&'a Buffer)",
        "value_size(module::Alias<u32>) + peak(module::f::<u32>)",
        "1 + 2 * 3 + (4 + 5) * 6",
        "value_size((x))",
        "ref_size(buffer) + value_size(Buffer)",
        "ref_size(&mut [u32]) + ref_size(&'a Buffer)",
        "peak(helper(false))",
        "peak(module::helper(count <= 4, !flag)) + peak(empty())",
    ] {
        let code = format!("fn f(x: u32) resources peak(memory) <= {budget}, {{}}");
        let parsed: ItemFn = parse_str(&code).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn bare_budget_names_are_quantities() {
    // Name resolution and restrictions on quantities belong to the verifier.
    let parsed: ItemFn = parse_str("fn f() resources peak(memory) <= BUDGET {}").unwrap();
    let verus_syn::ResourceExpr::Quantity(name) = parsed.sig.spec.resources.unwrap().budget else {
        panic!("expected a quantity")
    };
    assert_eq!(name, "BUDGET");
}

#[test]
fn peak_clause_is_distinct_from_calls_in_other_clauses() {
    for text in [
        "fn f(x: u32) requires peak(x), ensures peak(x), resources peak(memory) <= value_size(x), {}",
        "fn f(x: u32) requires peak(x) ensures peak(x) resources peak(memory) <= value_size(x) {}",
        "fn f<T>() where T: peak, resources peak(memory) <= 0 {}",
    ] {
        let parsed: ItemFn = parse_str(text).unwrap();
        assert!(parsed.sig.spec.resources.is_some());
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn memory_checkpoints_round_trip_alongside_logical_assertions() {
    for statement in [
        "assert(peak(memory) <= value_size(local) + peak(helper));",
        "assert(peak(memory) <= 2 * value_size([u32; 4]));",
        "assert(peak(memory) <= x);",
        "assert(current(memory) <= value_size(local));",
        "assert(current(local) <= 10);",
        "assert(peak(local) <= 10);",
        "assert(peak <= 10);",
        "assert(module::peak(memory) <= 10);",
        "assert(true) by { }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {statement} }}")).unwrap();
        let verus_syn::Stmt::Expr(verus_syn::Expr::Assert(assertion), _) = &parsed.block.stmts[0]
        else {
            panic!("expected an assertion")
        };
        assert_eq!(
            matches!(assertion.expr, verus_syn::AssertExpr::Memory(..)),
            statement.starts_with("assert(peak(memory)")
                || statement.starts_with("assert(current(memory)")
        );
        let printed = parsed.clone().to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn checkpoints_reject_proof_overrides_and_malformed_budgets() {
    for statement in [
        "assert(peak(memory) < 0);",
        "assert(current(memory) < 0);",
        "assert(current(memory) <= 0) by { }",
        "assert(peak(memory) == 0);",
        "assert(peak(memory) <= value_size(x)) by { }",
        "assert(peak(memory) <= 0) by(compute)",
        "assert(peak(memory) <= value_size(make()));",
        "assert(peak(memory) <= 4 - 1);",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {statement} }}")).is_err());
    }
}

#[test]
fn memory_sections_round_trip_and_end_statements() {
    for body in [
        "resources peak(memory) <= 0 {} let x = 1;",
        "resources peak(memory) <= unknown {}",
        "resources peak(memory) <= value_size(x) { resources peak(memory) <= 0 {} } resources peak(memory) <= 0 {};",
        "#[allow(unused)] resources peak(memory) <= 2 * (value_size([u32; 4]) + peak(helper)) { let x = 1; }",
        "let x = resources peak(memory) <= 0 {};",
        "if true { resources peak(memory) <= 0 {} } else { resources peak(memory) <= 0 {} }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {body} }}")).unwrap();
        let printed = parsed.clone().to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
    let parsed: ItemFn = parse_str("fn f() { peak(helper); }").unwrap();
    assert!(matches!(
        parsed.block.stmts[0],
        verus_syn::Stmt::Expr(verus_syn::Expr::Call(_), _)
    ));
}

#[test]
fn memory_sections_reject_invalid_budgets() {
    for body in [
        "resources peak(memory) <= value_size(make()) {}",
        "resources peak(memory) <= 4 - 1 {}",
        "resources peak(memory) <= 4;",
        "peak <= 4 {}",
        "resources current(memory) <= 4 {}",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {body} }}")).is_err());
    }
}

#[test]
fn conditional_resource_budgets_round_trip() {
    for budget in [
        "value_size(flag) + if flag { value_size([u32; 8]) } else { value_size([u32; 4]) }",
        "if count <= 4 { 16 } else { 32 }",
        "if flag { 4 } else { runtime_value }",
        "2 * (if a && !b { 32 } else { if b { 16 } else { 0 } })",
    ] {
        let parsed: ItemFn =
            parse_str(&format!("fn f() resources peak(memory) <= {budget}, {{}}")).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn conditional_resource_budgets_require_both_formula_branches() {
    for budget in ["if flag { 4 }", "if flag { let x = 4; x } else { 0 }"] {
        assert!(
            parse_str::<ItemFn>(&format!("fn f() resources peak(memory) <= {budget} {{}}"))
                .is_err()
        );
    }
}

#[test]
fn resources_remains_an_ordinary_name_outside_clauses() {
    for text in [
        "fn f(x: u32) requires resources(x), ensures resources(x), resources peak(memory) <= 4 {}",
        "fn f() { resources(); let x = resources { field: 0 }; }",
        "fn f<T>() where T: resources, resources peak(memory) <= 0 {}",
    ] {
        let parsed: ItemFn = parse_str(text).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}
