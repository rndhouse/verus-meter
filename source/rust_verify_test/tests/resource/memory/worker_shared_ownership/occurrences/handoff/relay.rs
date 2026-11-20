//! Reindex the receiving worker while another worker can retain the same allocation.
use super::{DROP_VECTORS, FINAL_TWO, GLOBAL, LEAVE_TWO, peer_program};
use crate::common::{assert_any_vir_error_msg, assert_vir_error_msg, assert_vir_error_msgs};

#[test]
fn an_indexed_receiver_preserves_the_original_allocation_visit() {
    for (name, body, receive, exact, short) in [
        (
            "consume",
            "drop(later)",
            "forwarded.pop().unwrap().join().unwrap(); drop(forwarded);",
            214,
            213,
        ),
        (
            "return",
            "later",
            "let link = forwarded.pop().unwrap().join().unwrap(); drop(forwarded);
         if n == 2 && b == 19 { assert(current(memory) <= 230); } drop(link);",
            230,
            229,
        ),
    ] {
        let relay = format!(
            "let relay = std::thread::spawn(move || {body});
            let mut forwarded = Vec::with_capacity(1); forwarded.push(relay); {receive}"
        );
        let finish = FINAL_TWO.replace("drop(later);", &relay);
        let program = peer_program(2, LEAVE_TWO, &format!("{finish}{DROP_VECTORS}"));
        assert_vir_error_msg(
            crate::verify_one_file(name, program.clone(), &[]).unwrap_err(),
            GLOBAL,
        );
        assert_vir_error_msgs(
            crate::verify_one_file(
                &format!("{name}_short"),
                program.replace(&format!("<= {exact}"), &format!("<= {short}")),
                &[],
            )
            .unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn an_indexed_receiver_can_be_the_last_owner() {
    // Two 59-byte allocations at n=2, b=19. Retaining the relay adds a
    // 24-byte vector, an 8-byte slot and a one-byte completion record.
    let end = r#"
        let carrier = handles.pop().unwrap().join().unwrap();
        let peer = peers.pop().unwrap().join().unwrap();
        let mut forwarded = Vec::with_capacity(1);
        let relay = std::thread::spawn(move || drop(CAPTURE)); forwarded.push(relay);
        drop(OTHER);
        if n == 2 && b == 19 { assert(current(memory) <= 239); }
        forwarded.pop().unwrap().join().unwrap(); drop(forwarded);
        if n == 2 && b == 19 { assert(current(memory) <= 147); }
        let carrier = handles.pop().unwrap().join().unwrap(); drop(carrier);
        let peer = peers.pop().unwrap().join().unwrap(); drop(peer);
    "#;
    for (capture, other) in [("peer", "carrier"), ("carrier", "peer")] {
        let end = end.replace("CAPTURE", capture).replace("OTHER", other);
        let program = peer_program(2, LEAVE_TWO, &format!("{end}{DROP_VECTORS}"));
        assert_vir_error_msg(
            crate::verify_one_file(capture, program.clone(), &[]).unwrap_err(),
            GLOBAL,
        );
        assert_vir_error_msgs(
            crate::verify_one_file(
                &format!("{capture}_short"),
                program.replace("<= 239", "<= 238"),
                &[],
            )
            .unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
        if capture == "peer" {
            let lost = program.replace("forwarded.pop().unwrap().join().unwrap();", "");
            assert_any_vir_error_msg(
                crate::verify_one_file("missing_relay", lost, &[]).unwrap_err(),
                "cannot discard outstanding worker handles",
            );
        }
    }
}

#[test]
fn collecting_a_relay_selects_its_own_capture_from_two_visits() {
    // The last pushed relay holds the older allocation. Its original peer
    // still owns it. The newer allocation is now held solely by the other relay.
    let finish = r#"
        let mut relays = Vec::with_capacity(2);
        let newer = handles.pop().unwrap().join().unwrap();
        relays.push(std::thread::spawn(move || drop(newer)));
        let older = handles.pop().unwrap().join().unwrap();
        relays.push(std::thread::spawn(move || drop(older)));
        drop(peers.pop().unwrap().join().unwrap());
        relays.pop().unwrap().join().unwrap();
        if n == 2 && b == 19 { assert(current(memory) <= 246); }
        drop(peers.pop().unwrap().join().unwrap());
        if n == 2 && b == 19 { assert(current(memory) <= 186); }
        relays.pop().unwrap().join().unwrap(); drop(relays);
    "#;
    let program = peer_program(2, LEAVE_TWO, &format!("{finish}{DROP_VECTORS}"));
    assert_vir_error_msg(
        crate::verify_one_file("two_relays", program.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    let short =
        crate::verify_one_file("two_relays_short", program.replace("<= 246", "<= 245"), &[])
            .unwrap_err();
    let checkpoint = crate::common::relevant_error_span(&short.errors[0].spans);
    assert!(checkpoint.text.iter().any(|line| line.text.contains("current(memory) <= 245")));
    assert_vir_error_msgs(short, &["conditional memory budget exceeded", GLOBAL]);
}
