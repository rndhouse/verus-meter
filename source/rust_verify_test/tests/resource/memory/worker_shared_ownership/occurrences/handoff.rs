//! Retain a backing after its carrying handle ends. Only peers from the same
//! executable allocation visit can discharge that backing.

use super::{DROP_VECTORS, GLOBAL, PRODUCT, peer_program};
use crate::common::{assert_vir_error_msg, assert_vir_error_msgs};

// Leave two visits outstanding without specializing the publication loop to two workers.
const LEAVE_TWO: &str = r#"
    while handles.len() > 2 invariant handles.len() == peers.len(), 2 <= handles.len() <= n,
        decreases handles.len(),
    {
        proof { product(n as int, 41 + b as int); }
        let first = handles.pop().unwrap().join().unwrap();
        let second = peers.pop().unwrap().join().unwrap();
        drop(first); drop(second);
    }
"#;

#[test]
fn an_equal_sized_buffer_from_another_visit_cannot_take_the_charge() {
    let final_two = r#"
        let deferred = peers.pop().unwrap();
        let earlier_peer = peers.pop().unwrap().join().unwrap();
        let later = handles.pop().unwrap().join().unwrap();
        drop(later);
        if n == 2 && b == 19 { assert(current(memory) <= 222); }
        drop(earlier_peer);
        // The older visit's peer ended. Its carrier and the newer visit's
        // deferred backing still own distinct 59-byte allocations.
        if n == 2 && b == 19 { assert(current(memory) <= 214); }
        let later_peer = deferred.join().unwrap(); drop(later_peer);
        if n == 2 && b == 19 { assert(current(memory) <= 146); }
        let earlier = handles.pop().unwrap().join().unwrap(); drop(earlier);
    "#;
    let program = peer_program(2, LEAVE_TWO, &format!("{final_two}{DROP_VECTORS}"));
    assert_vir_error_msg(
        crate::verify_one_file("pending_visit", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    for (name, live, smaller) in [
        ("before_peer", "<= 222", "<= 221"),
        ("other_visit", "<= 214", "<= 213"),
        ("remaining", "<= 146", "<= 145"),
    ] {
        assert_vir_error_msgs(
            crate::verify_one_file(name, program.replace(live, smaller), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn two_deferred_backings_retire_independently() {
    let finish = r#"
        let later = handles.pop().unwrap().join().unwrap(); drop(later);
        let earlier = handles.pop().unwrap().join().unwrap(); drop(earlier);
        // Both charges now reside with the publisher on behalf of unjoined peers.
        if n == 2 && b == 19 { assert(current(memory) <= 206); }
        let later_peer = peers.pop().unwrap().join().unwrap(); drop(later_peer);
        if n == 2 && b == 19 { assert(current(memory) <= 146); }
        let earlier_peer = peers.pop().unwrap().join().unwrap(); drop(earlier_peer);
        if n == 2 && b == 19 { assert(current(memory) <= 86); }
    "#;
    let program = peer_program(2, LEAVE_TWO, &format!("{finish}{DROP_VECTORS}"));
    assert_vir_error_msg(
        crate::verify_one_file("both_deferred", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    assert_vir_error_msgs(
        crate::verify_one_file("both_deferred_short", program.replace("<= 206", "<= 205"), &[])
            .unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}

#[test]
fn a_peer_in_its_vector_retains_the_backing_after_the_carrier_ends() {
    for (name, carrier_returns, peer_returns) in [
        ("waiting_peer_returns", true, true),
        ("waiting_peer_consumes", true, false),
        ("carrier_consumes", false, true),
    ] {
        let peer_join = "peers.pop().unwrap().join().unwrap()";
        let release_peer = if peer_returns {
            format!("let retained = {peer_join}; drop(retained);")
        } else {
            format!("{peer_join};")
        };
        let carrier_join = "handles.pop().unwrap().join().unwrap()";
        let (join_carrier, drop_carrier) = if carrier_returns {
            (format!("let result = {carrier_join};"), "drop(result);")
        } else {
            (format!("{carrier_join};"), "")
        };
        let collect = format!(
            r#"
            while handles.len() > 2 invariant handles.len() == peers.len(), 2 <= handles.len() <= n,
                decreases handles.len(),
            {{
                proof {{ product(n as int, 41 + b as int); }}
                {join_carrier} {release_peer} {drop_carrier}
            }}
            {join_carrier} {drop_carrier}
            // Both 59-byte backings remain. Only the carrier's completion tag has ended.
            if n == 2 && b == 19 {{ assert(current(memory) <= 207); }}
            {release_peer}
            // This removes one more tag and the matching backing.
            if n == 2 && b == 19 {{ assert(current(memory) <= 147); }}
            {join_carrier} {drop_carrier} {release_peer}
            "#
        );
        let mut program = peer_program(2, &collect, DROP_VECTORS);
        if !peer_returns {
            program = program.replace("move || alias", "move || drop(alias)");
        }
        if !carrier_returns {
            program = program.replace("move || root", "move || drop(root)");
        }
        assert_vir_error_msg(
            crate::verify_one_file(name, program.clone(), &[]).unwrap_err(),
            GLOBAL,
        );
        assert_vir_error_msgs(
            crate::verify_one_file(
                &format!("{name}_early"),
                program.replace("<= 207", "<= 206"),
                &[],
            )
            .unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn every_peer_of_the_same_visit_must_retire() {
    // Each visit publishes three independent workers for one allocation.
    // The result from the carrier drops before either peer is collected.
    let program = format!(
        r#"
        use vstd::prelude::*;
        verus! {{
        {PRODUCT}
        fn fresh(n: u16, b: u16)
            requires n >= 2, 0 <= n as int * (41 + b as int) <= 5000000000int,
            resources peak(memory) <= n * 26 + n * (41 + b) + 256
        {{
            proof {{ product(n as int, 41 + b as int); }}
            let mut carriers = Vec::with_capacity(n as usize);
            let mut peers = Vec::with_capacity(n as usize);
            let mut siblings = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, carriers.len() == i, peers.len() == i, siblings.len() == i,
                decreases n - i,
            {{
                proof {{ product(n as int, 41 + b as int); }}
                let root = std::sync::Arc::new(Vec::<u8>::with_capacity(b as usize));
                let sibling = root.clone(); siblings.push(std::thread::spawn(move || sibling));
                let peer = root.clone(); peers.push(std::thread::spawn(move || peer));
                carriers.push(std::thread::spawn(move || root));
                i += 1;
            }}
            while carriers.len() > 2 invariant carriers.len() == peers.len(),
                carriers.len() == siblings.len(), 2 <= carriers.len() <= n, decreases carriers.len(),
            {{
                proof {{ product(n as int, 41 + b as int); }}
                let carrier = carriers.pop().unwrap().join().unwrap();
                let peer = peers.pop().unwrap().join().unwrap();
                let sibling = siblings.pop().unwrap().join().unwrap();
                drop(sibling); drop(carrier); drop(peer);
            }}
            let carrier = carriers.pop().unwrap().join().unwrap(); drop(carrier);
            let peer = peers.pop().unwrap().join().unwrap(); drop(peer);
            // A sibling still owns the newer 59-byte backing.
            if n == 2 && b == 19 {{ assert(current(memory) <= 248); }}
            let sibling = siblings.pop().unwrap().join().unwrap(); drop(sibling);
            if n == 2 && b == 19 {{ assert(current(memory) <= 188); }}
            let carrier = carriers.pop().unwrap().join().unwrap(); drop(carrier);
            let peer = peers.pop().unwrap().join().unwrap(); drop(peer);
            let sibling = siblings.pop().unwrap().join().unwrap(); drop(sibling);
            drop(carriers); drop(peers); drop(siblings);
            assert(current(memory) <= 6);
        }}
        }}
        "#
    );
    assert_vir_error_msg(
        crate::verify_one_file("two_peers", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    assert_vir_error_msgs(
        crate::verify_one_file("two_peers_short", program.replace("<= 248", "<= 247"), &[])
            .unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}
