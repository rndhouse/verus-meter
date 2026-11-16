//! Expansion must follow source size rather than repeated symbolic substitution.
use super::expand;
use quote::quote;
use verus_syn::Item;

fn expanded_size(bindings: usize, helpers: bool) -> usize {
    let formula = if helpers {
        let mut declarations = "spec fn step0(n: nat) -> nat { n }\n".to_owned();
        for level in 1..=bindings {
            let previous = level - 1;
            declarations.push_str(&format!(
                "spec fn step{level}(n: nat) -> nat {{ step{previous}(n) + step{previous}(n) }}\n"
            ));
        }
        format!("{declarations} spec fn budget(n: nat) -> nat {{ 1024 + step{bindings}(n) }}")
    } else {
        let declarations = "let n = n + n;\n".repeat(bindings);
        format!("spec fn budget(n: nat) -> nat {{ {declarations} 1024 + n }}")
    };
    let file: verus_syn::File = verus_syn::parse_str(&format!(
        "{formula} #[queryable_peak_memory] fn work(n: u8) resources peak(memory) <= budget(n as nat) {{}}"
    ))
    .unwrap();
    let mut items = file.items;
    expand(&mut items);
    assert!(!items.iter().any(|item| matches!(item, Item::Verbatim(tokens) if tokens.to_string().contains("compile_error"))));
    quote!(#(#items)*).to_string().len()
}

#[test]
fn shared_bindings_and_identical_helper_calls_have_linear_expansions() {
    for helpers in [false, true] {
        let smaller = expanded_size(12, helpers);
        let larger = expanded_size(24, helpers);
        assert!(
            larger < 3 * smaller,
            "expansion grew from {smaller} to {larger} bytes",
            smaller = smaller,
            larger = larger
        );
    }
}
