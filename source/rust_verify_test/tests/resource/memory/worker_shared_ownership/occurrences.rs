//! Different visits to Arc::new have independent backings. Capture, publication
//! and join must preserve the key of the allocation actually returned.

use super::GLOBAL;
use crate::common::{assert_vir_error_msg, assert_vir_error_msgs};

// Only mathematical facts about products. All allocation, clone, and drop
// evidence comes from the executable program below.
const PRODUCT: &str = r#"
    proof fn product(n: int, w: int)
        requires 0 <= w,
        ensures
            forall|k: int| #[trigger] (w * k) == k * w,
            forall|k: int| #[trigger] ((k + 1) * w) == k * w + w,
            forall|k: int| 0 <= k <= n ==> #[trigger] (k * w) <= n * w,
            forall|k: int| 0 <= k < n ==> #[trigger] (k * w) + w <= n * w,
    {
        use vstd::arithmetic::mul::*;
        assert forall|k: int| #[trigger] (w * k) == k * w by {
            lemma_mul_is_commutative(w, k);
        }
        assert forall|k: int| #[trigger] ((k + 1) * w) == k * w + w by {
            lemma_mul_is_distributive_add_other_way(w, k, 1);
        }
        assert forall|k: int| 0 <= k <= n implies #[trigger] (k * w) <= n * w by {
            lemma_mul_inequality(k, n, w);
        }
        assert forall|k: int| 0 <= k < n implies #[trigger] (k * w) + w <= n * w by {
            lemma_mul_is_distributive_add_other_way(w, k, 1);
            lemma_mul_inequality(k + 1, n, w);
        }
    }
"#;

fn program(minimum: u16, publication: &str, collection: &str) -> String {
    format!(
        r#"
        use vstd::prelude::*;
        verus! {{
        {PRODUCT}
        fn fresh(n: u16, b: u16)
            requires n >= {minimum}, 0 <= n as int * (41 + b as int) <= 5000000000int,
            resources peak(memory) <= n * 8 + n * (41 + b) + 192
        {{
            proof {{ product(n as int, 41 + b as int); }}
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {{
                proof {{ product(n as int, 41 + b as int); }}
                let root = std::sync::Arc::new(Vec::<u8>::with_capacity(b as usize));
                {publication}
                handles.push(job);
                i += 1;
            }}
            {collection}
        }}
        }}
    "#
    )
}

const PUBLISH: &str = "let job = std::thread::spawn(move || root);";

const COLLECT: &str = r#"
    if n == 0 { assert(current(memory) <= 30); return; }
    if n == 2 && b == 19 { assert(current(memory) <= 166); }
    while handles.len() > 1 invariant 1 <= handles.len() <= n, decreases handles.len(), {
        proof { product(n as int, 41 + b as int); }
        let result = handles.pop().unwrap().join().unwrap();
        drop(result);
    }
    let last = handles.pop().unwrap().join().unwrap();
    drop(handles);
    if b == 19 { assert(current(memory) <= 73); }
    drop(last);
    assert(current(memory) <= 6);
"#;

#[test]
fn fresh_buffers_charge_each_outstanding_visit() {
    let program = program(0, PUBLISH, COLLECT);
    assert_vir_error_msg(
        crate::verify_one_file("fresh_buffers", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );

    // n, b and i occupy 6 bytes. With two pending workers add 24 for the
    // vector, 16 for its slots, 2 completion tags and 2 * (16 + 24 + 19)
    // for the Arc backings. A bound of 107 allows only one of those backings.
    for (name, bound) in [("fresh_short", "165"), ("one_backing", "107")] {
        let short = program.replace("<= 166", &format!("<= {bound}"));
        assert_vir_error_msgs(
            crate::verify_one_file(name, short, &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn two_retained_results_release_their_own_visit() {
    // Two workers run with the same allocation on each visit. The peer's
    // returned clone is dropped while the other worker is outstanding.
    let publish = r#"
        let alias = root.clone();
        let peer = std::thread::spawn(move || alias);
        let job = std::thread::spawn(move || root);
        let returned = peer.join().unwrap();
        drop(returned);
    "#;
    let collect = r#"
        while handles.len() > 2 invariant 2 <= handles.len() <= n, decreases handles.len(), {
            proof { product(n as int, 41 + b as int); }
            let result = handles.pop().unwrap().join().unwrap();
            drop(result);
        }
        let first = handles.pop().unwrap().join().unwrap();
        let second = handles.pop().unwrap().join().unwrap();
        drop(handles);
        if b == 19 { assert(current(memory) <= 140); }
        drop(first);
        if b == 19 { assert(current(memory) <= 73); }
        drop(second);
        assert(current(memory) <= 6);
    "#;
    let program = program(2, publish, collect);
    assert_vir_error_msg(
        crate::verify_one_file("two_retained_results", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    for (name, bound, short) in [("both_live", "<= 140", "<= 139"), ("one_live", "<= 73", "<= 72")]
    {
        assert_vir_error_msgs(
            crate::verify_one_file(name, program.replace(bound, short), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}
