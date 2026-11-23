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
