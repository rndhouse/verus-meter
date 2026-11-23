//! Permissioned atomic operands are executable source values. Their linear
//! permissions erase, and either compare-exchange outcome can execute.
use super::super::support::{exact_peak, rejects, verifies};

#[test]
fn atomic_locations_and_permissions() {
    verifies(
        "atomic_source_layout",
        r#"
        use vstd::atomic::*;
        fn f() resources peak(memory) <= 0 {
            assert(value_size(PAtomicBool) == 1);
            assert(value_size(PAtomicUsize) == 8);
            assert(value_size(Tracked<PermissionUsize>) == 0);
        }
    "#,
    );
    exact_peak(
        "atomic_source_lifetimes",
        r#"
        use vstd::atomic::*;
        fn f() resources peak(memory) <= BUDGET {
            let (a, Tracked(mut p)) = PAtomicBool::new(false);
            let old = a.load(Tracked(&p));
            a.store(Tracked(&mut p), true);
        }
    "#,
        // Location, old value, store receiver and boolean argument.
        11,
    );
}

#[test]
fn cas_accounts_for_both_outcomes() {
    let body = r#"
        use vstd::atomic::*;
        fn f(a: &PAtomicBool, Tracked(p): Tracked<&mut PermissionBool>) -> bool
            requires old(p).is_for(*a),
            resources peak(memory) <= BUDGET
        {
            let result = a.compare_exchange(Tracked(p), false, true);
            BODY
        }
    "#;
    exact_peak("atomic_cas", &body.replace("BODY", "result.is_ok()"), 20);
    exact_peak(
        "atomic_failed_attempt",
        &body.replace(
            "BODY",
            "match result { Ok(_) => true, Err(_) => { let scratch = [0u8; 64]; false } }",
        ),
        75,
    );
    rejects(
        "atomic_no_assumed_success",
        &body.replace("BUDGET", "128").replace("BODY", "assert(result is Ok); true"),
        "assertion failed",
    );
}

#[test]
fn atomic_counter_operands_overlap_the_return_destination() {
    exact_peak(
        "atomic_counter_word",
        r#"
        use vstd::atomic::*;
        fn f(a: &PAtomicUsize, Tracked(p): Tracked<&mut PermissionUsize>, n: usize) -> usize
            requires old(p).is_for(*a),
            resources peak(memory) <= BUDGET
        { a.fetch_add_wrapping(Tracked(p), n) }
        "#,
        40,
    );
}

#[test]
fn checked_wrappers_use_their_verified_bodies() {
    let body = r#"
        use vstd::atomic::*;
        fn f(a: &PAtomicUsize, Tracked(p): Tracked<&mut PermissionUsize>, n: usize) -> usize
            requires old(p).is_for(*a), LIMIT
            resources peak(memory) <= BUDGET
        { a.fetch_add(Tracked(p), n) }
    "#;
    exact_peak(
        "atomic_checked_helper",
        &body.replace("LIMIT", "old(p).view().value <= usize::MAX - n,"),
        56,
    );
    rejects(
        "atomic_checked_helper_overflow",
        &body.replace("LIMIT", "").replace("BUDGET", "56"),
        "precondition not satisfied",
    );
}

#[test]
fn invariant_opening_preserves_runtime_storage_and_functional_checks() {
    let body = r#"
        use vstd::invariant::*;
        struct Pred;
        impl InvariantPredicate<(), bool> for Pred {
            open spec fn inv(_: (), flag: bool) -> bool { flag }
        }
        fn f(Tracked(i): Tracked<&AtomicInvariant<(), bool, Pred>>) resources peak(memory) <= BUDGET {
            open_atomic_invariant!(i => state => {
                let scratch = 72u128;
                PROOF
            });
        }
    "#;
    exact_peak("atomic_invariant_workspace", &body.replace("PROOF", "assert(state);"), 16);
    rejects(
        "atomic_invariant_preservation",
        &body.replace("BUDGET", "16").replace("PROOF", "proof { state = false; }"),
        "cannot show invariant holds at end of block",
    );
    exact_peak(
        "atomic_argument_before_erasure",
        r#"
        use vstd::invariant::*;
        fn f() resources peak(memory) <= BUDGET {
            spend_open_invariant_credit({
                let scratch = [0u8; 41];
                create_open_invariant_credit()
            });
        }
    "#,
        41,
    );
}

#[test]
fn ghost_atomic_uses_the_real_location_and_macro_operands() {
    let body = r#"
        use vstd::atomic_ghost::*;
        struct Pred;
        impl AtomicInvariantPredicate<(), bool, ()> for Pred {
            open spec fn atomic_inv(_: (), _: bool, _: ()) -> bool { true }
        }
        fn f(a: &AtomicBool<(), (), Pred>) -> bool
            requires a.well_formed(),
            resources peak(memory) <= BUDGET
        {
            assert(value_size(AtomicBool<(), (), Pred>) == 1);
            BODY
        }
    "#;
    exact_peak(
        "ghost_atomic_load",
        &body.replace("BODY", "atomic_with_ghost!(a => load(); ghost g => {})"),
        25,
    );
    exact_peak("ghost_atomic_cas", &body.replace("BODY", "let result = atomic_with_ghost!(a => compare_exchange(false, true); ghost g => {}); result.is_ok()"), 30);
}

#[test]
fn an_erased_initializer_preserves_the_following_owned_field() {
    exact_peak(
        "atomic_record_owns_its_payload",
        r#"
        use vstd::atomic::*;
        struct Packet { a: PAtomicBool, marker: Ghost<int>, payload: Box<[u8; 64]> }
        fn f() resources peak(memory) <= BUDGET {
            let (a, Tracked(_p)) = PAtomicBool::new(false);
            let packet = Packet { marker: Ghost(7int), payload: Box::new([0u8; 64]), a };
            let data = packet.payload;
            drop(data);
        }
    "#,
        81,
    );
}
