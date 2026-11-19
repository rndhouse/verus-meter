//! Different visits to Arc::new have independent backings. Capture, publication
//! and join must preserve the key of the allocation actually returned.

mod handoff;

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

/// Each visit sends the same Arc to two independently retained workers.
/// At n = 2, b = 19 there are four handles and exactly two allocated buffers.
fn peer_program(minimum: u16, collect: &str, cleanup: &str) -> String {
    format!(
        r#"
        use vstd::prelude::*;
        verus! {{
        {PRODUCT}
        fn fresh(n: u16, b: u16)
            requires n >= {minimum}, 0 <= n as int * (41 + b as int) <= 5000000000int,
            resources peak(memory) <= n * 17 + n * (41 + b) + 256
        {{
            proof {{ product(n as int, 41 + b as int); }}
            let mut handles = Vec::with_capacity(n as usize);
            let mut peers = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant handles.len() == i, peers.len() == i, i <= n, decreases n - i, {{
                proof {{ product(n as int, 41 + b as int); }}
                let root = std::sync::Arc::new(Vec::<u8>::with_capacity(b as usize));
                let alias = root.clone();
                peers.push(std::thread::spawn(move || alias));
                handles.push(std::thread::spawn(move || root));
                i += 1;
            }}
            if n == 2 && b == 19 {{ assert(current(memory) <= 208); }}
            {collect}
            {cleanup}
            assert(current(memory) <= 6);
        }}
        }}
    "#
    )
}

const DROP_VECTORS: &str = "drop(peers); drop(handles);";

const PAIRED: &str = r#"
    while handles.len() > 0 invariant handles.len() == peers.len(), handles.len() <= n,
        decreases handles.len(),
    {
        proof { product(n as int, 41 + b as int); }
        let first = handles.pop().unwrap().join().unwrap();
        let second = peers.pop().unwrap().join().unwrap();
        drop(first);
        // Both vector buffers are still reserved. The final alias occupies
        // 8 bytes and retains 59 more. Total = 6 + 48 + 32 + 8 + 59.
        if handles.len() == 0 && n == 2 && b == 19 { assert(current(memory) <= 153); }
        drop(second);
    }
"#;

#[test]
fn independently_stored_peers_charge_once_in_either_drop_order() {
    let program = peer_program(0, PAIRED, DROP_VECTORS);
    let reverse = PAIRED
        .replace("let first = handles", "let second = handles")
        .replace("let second = peers", "let first = peers");
    for (name, source) in
        [("paired", program.clone()), ("reverse", peer_program(0, &reverse, DROP_VECTORS))]
    {
        assert_vir_error_msg(crate::verify_one_file(name, source, &[]).unwrap_err(), GLOBAL);
    }
    for (name, bound, short) in
        [("four_jobs", "<= 208", "<= 207"), ("final_alias", "<= 153", "<= 152")]
    {
        assert_vir_error_msgs(
            crate::verify_one_file(name, program.replace(bound, short), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn collecting_a_whole_peer_population_preserves_the_buffers() {
    for (name, worker, receive) in [
        (
            "peer_returns_alias",
            "alias",
            "let alias = peers.pop().unwrap().join().unwrap(); drop(alias);",
        ),
        ("peer_consumes_alias", "{ drop(alias); }", "peers.pop().unwrap().join().unwrap();"),
    ] {
        let collect = format!(
            r#"
            while peers.len() > 0 invariant peers.len() <= n, decreases peers.len(), {{
                proof {{ product(n as int, 41 + b as int); }}
                {receive}
            }}
            drop(peers);
            {COLLECT}
        "#
        );
        let program =
            peer_program(0, &collect, "").replace("move || alias", &format!("move || {worker}"));
        assert_vir_error_msg(crate::verify_one_file(name, program, &[]).unwrap_err(), GLOBAL);
    }
}

#[test]
fn joining_restores_the_capacity_from_the_selected_visit() {
    let program = r#"
        use vstd::prelude::*;
        verus! {
        fn collect(n: u16, observe: u16) requires 2 <= n <= 3, resources peak(memory) <= 512 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant 2 <= n <= 3, handles.len() == i, i <= n, decreases n - i, {
                let root = std::sync::Arc::new(Vec::<u8>::with_capacity(i as usize + 7));
                handles.push(std::thread::spawn(move || root));
                i += 1;
            }
            while handles.len() > 2 invariant 2 <= n <= 3, 2 <= handles.len() <= n,
                decreases handles.len(),
            {
                let result = handles.pop().unwrap().join().unwrap();
                drop(result);
            }
            let later = handles.pop().unwrap().join().unwrap();
            let earlier = handles.pop().unwrap().join().unwrap();
            drop(handles);
            if observe == 1 { assert(current(memory) <= 117); }
            drop(later);
            // The first visit requested 7 bytes. Its result has an 8-byte
            // handle, a 16-byte control block and a 24-byte Vec header.
            if observe == 1 { assert(current(memory) <= 61); }
            drop(earlier);
            assert(current(memory) <= 6);
        }
        }
    "#;
    assert_vir_error_msg(
        crate::verify_one_file("vary_capacity", program.into(), &[]).unwrap_err(),
        GLOBAL,
    );
    assert_vir_error_msgs(
        crate::verify_one_file("vary_short", program.replace("<= 61", "<= 60"), &[]).unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}
