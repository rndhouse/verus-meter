use quote::ToTokens;
use verus_prettyplease as prettyplease;
use verus_syn::visit::Visit;

#[derive(Default)]
struct Contracts(Vec<(String, String)>);

impl<'ast> Visit<'ast> for Contracts {
    fn visit_signature(&mut self, signature: &'ast verus_syn::Signature) {
        self.0.push((
            signature.spec.to_token_stream().to_string(),
            signature
                .generics
                .where_clause
                .to_token_stream()
                .to_string(),
        ));
    }
}

#[test]
fn resource_contracts_preserve_surrounding_specs_and_where_clauses() {
    for source in [
        "fn f(v: &Vec<u32>, n: usize) requires n > 0, ensures n > 0, resources peak(memory) <= 16, {}",
        "fn f<T>(v: &Vec<T>) where T: Copy, resources peak(memory) <= 8 {}",
        "trait Helpers { fn f(v: &Vec<u32>) resources peak(memory) <= 8; }",
        "impl Helpers { fn f(v: &Vec<u32>) resources peak(memory) <= 8 {} }",
    ] {
        let file = verus_syn::parse_file(source).unwrap();
        let pretty = prettyplease::unparse(&file);
        let reparsed = verus_syn::parse_file(&pretty).unwrap();
        let mut before = Contracts::default();
        let mut after = Contracts::default();
        before.visit_file(&file);
        after.visit_file(&reparsed);
        assert_eq!(before.0.len(), 1, "missing original signature: {source}");
        assert_eq!(after.0.len(), 1, "missing printed signature: {source}");
        assert_eq!(before.0, after.0);
        assert_eq!(pretty, prettyplease::unparse(&reparsed));
    }
}
