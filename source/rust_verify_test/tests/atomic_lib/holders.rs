use super::*;

test_verify_one_file! {
    #[test] a_forwarded_permit_retains_its_instance_in_a_worker code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{Holder, BoundedHolder};
        use vstd::resource::semaphore::{Permit, Semaphore};
        use std::sync::Arc;

        verus! {
            fn forward<'a>(p: Permit<'a>, keep: bool) -> (result: Option<Permit<'a>>)
                ensures
                    result matches Some(q) ==> q.semaphore() == p.semaphore(),
                    result.is_some() == keep,
            {
                if keep { Some(p) } else { p.release(); None }
            }

            fn work(k: usize, retain: bool) {
                let s = Arc::new(Semaphore::new(k));
                let worker = vstd::thread::spawn(move || {
                    if let Some(p) = s.try_acquire() {
                        assert(k > 0 && p.instance_id() == s.id() && p.capacity() == k);
                        if let Some(q) = forward(p, retain) {
                            assert(q.instance_id() == s.id());
                            q.release();
                        }
                    }
                });
                let _ = worker.join();
                let zero = Semaphore::new(0);
                let empty = zero.try_acquire();
                assert(empty.is_none());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] a_permit_does_not_justify_another_capacity code! {
        use vstd::prelude::*;
        use vstd::resource::semaphore::Semaphore;
        use vstd::resource::holder::BoundedHolder;
        verus! {
            fn wrong() {
                let a = Semaphore::new(2);
                let b = Semaphore::new(1);
                let p = a.acquire();
                assert(p.capacity() == b.capacity()); // FAILS
                p.release();
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] an_unrestricted_holder_cannot_prove_exclusion code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{BoundedHolder, Holder};
        use vstd::resource::Loc;
        verus! {
            struct Fake { domain: Ghost<Loc> }
            impl Holder for Fake {
                closed spec fn instance_id(&self) -> Loc { self.domain@ }
            }
            impl BoundedHolder for Fake {
                open spec fn capacity(&self) -> nat { 1 }
                proof fn population_bound(tracked population: Seq<Self>, id: Loc, capacity: nat) {
                    assert(population.len() <= capacity); // FAILS
                }
            }
        }
    } => Err(e) => assert_one_fails(e)
}

#[test]
fn a_custom_exclusive_protocol_needs_the_successful_atomic_transition() {
    let source = include_str!("exclusive.verus.rs");
    verify_one_file("exclusive_holder", source.into(), &[]).unwrap();
    for (method, peak) in [("acquire", 30), ("release", 33)] {
        let short = peak - 1;
        let body =
            source.replace(&format!("peak(memory) <= {peak}"), &format!("peak(memory) <= {short}"));
        let error = verify_one_file(&format!("custom_{method}_bytes"), body, &[]).unwrap_err();
        crate::common::assert_vir_error_msg(
            error,
            &format!("peak {peak} bytes exceeds budget {short} bytes"),
        );
    }
    let broken = source.replace("if success.is_ok()", "if success.is_err()");
    let err = verify_one_file("failed_cas_holder", broken, &[]).unwrap_err();
    assert!(err.errors.iter().any(|d| d.message.contains("precondition not satisfied")));
}

#[test]
fn custom_guard_coverage_follows_the_owned_value_and_allocation() {
    let source = include_str!("exclusive.verus.rs");
    let trace =
        verify_one_file("custom_guard_coverage", source.into(), &["--trace", "--no-cheating"])
            .unwrap();
    let note = |message: &str| trace.notes.iter().any(|n| n.message == message);
    assert!(note("64-byte allocation only observed within intact holder input 0"));
    assert!(note("64-byte allocation also observed outside intact holder input 0"));
    assert!(note("67-byte allocation only observed within intact holder input 0"));
    assert!(note("66-byte allocation also observed outside intact holder input 0"));
    assert!(
        !trace
            .notes
            .iter()
            .any(|n| n.message.starts_with("67-byte allocation") && n.message.ends_with("input 1"))
    );
    assert!(note("68-byte allocation only observed within intact holder local"));
    assert!(
        !trace
            .notes
            .iter()
            .any(|n| n.message.starts_with("68-byte allocation")
                && n.message.contains("holder input"))
    );
    assert!(note("61-byte allocation only observed within intact holder input 0"));
    assert!(note("63-byte allocation only observed within intact holder input 0"));
    assert!(note("dynamic storage region also observed outside intact holder input 0"));
    assert!(note("51-byte allocation also observed outside intact holder input 0"));
    assert!(!trace.notes.iter().any(|n| n.message.starts_with("52-byte allocation")));
    assert!(note("dynamic storage region only observed within intact holder input 0"));
    assert!(note("45-byte allocation only observed within intact holder local"));
    assert!(!trace.notes.iter().any(|n| n.message.starts_with("46-byte allocation")));
    let at_call = |line: &str, message: &str| {
        trace.notes.iter().any(|n| {
            n.message == message
                && n.spans.iter().flat_map(|s| &s.text).any(|s| s.text.trim() == line)
        })
    };
    assert!(at_call("scratch(retained);", "checked helper phase with intact holder input 1"));
    assert!(!at_call("scratch(retained);", "checked helper phase with intact holder input 0"));
    assert!(at_call("scratch(g);", "checked helper phase with intact holder local"));
}

#[test]
fn returning_the_other_guard_changes_the_proved_issuer() {
    let source = include_str!("exclusive.verus.rs")
        .replace("keep_guard(b, a, keep)", "keep_guard(a, b, keep)");
    let trace = verify_one_file("wrong_returned_issuer", source, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert!(
        trace
            .notes
            .iter()
            .any(|n| n.message == "67-byte allocation only observed within intact holder input 1")
    );
    assert_vir_error_msg(trace, "assertion failed");
}

#[test]
fn symbolic_scratch_and_release_each_need_their_own_peak() {
    let source = include_str!("exclusive.verus.rs");
    for (case, allowance) in [
        ("empty", "if n == 0 { 40 } else { n + 40 }"),
        ("reserved", "if n == 0 { 41 } else { n + 39 }"),
    ] {
        let short = source.replace("if n == 0 { 41 } else { n + 40 }", allowance);
        let trace = verify_one_file(&format!("short_holder_{case}"), short, &["--no-cheating"])
            .unwrap_err();
        crate::common::assert_vir_error_msg(trace, "conditional memory budget exceeded");
    }
}

#[test]
fn a_bodyless_population_proof_supplies_no_memory_evidence() {
    let source = include_str!("exclusive.verus.rs").replace(
        "    proof fn population_bound(",
        "    #[verifier::external_body]\n    proof fn population_bound(",
    );
    let trace = verify_one_file("unchecked_holder_body", source, &["--trace"]).unwrap();
    assert!(!trace.notes.iter().any(|n| n.message.contains("intact holder")));
}

#[test]
fn a_worker_passes_its_actual_moved_guard_to_the_helper() {
    let source = include_str!("exclusive.verus.rs").replace(
        "fn work() {",
        r#"
        fn publish(first: Guard<'static>, carried: Guard<'static>) resources peak(memory) <= 1024 {
            first.leave();
            let task = move || {
                let overlap = Box::new([0u8; 41]);
                scratch(carried);
                drop(overlap);
            };
            let worker = vstd::thread::spawn(task);
            let done = worker.join();
        }
        fn work() {"#,
    );
    let returned = source.replace(
        "scratch(carried);",
        r#"
                let moved = carry(carried);
                let data = Box::new([0u8; 69]);
                drop(data);
                scratch(moved);"#,
    );
    let trace = verify_one_file("worker_returned_holder", returned, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
    assert!(trace.notes.iter().any(|n| n.message == "69-byte allocation only observed within intact holder capture 0"));
    let shared = source.replace(
        "fn publish(first: Guard<'static>, carried: Guard<'static>)",
        "fn inspect(_shared: &Guard<'_>) resources peak(memory) <= 80 { let b = Box::new([0u8; 42]); drop(b); }
fn publish(first: Guard<'static>, carried: &'static Guard<'static>)",
    ).replace("scratch(carried);", "inspect(carried);");
    let trace = verify_one_file("worker_borrowed_holder", shared, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
    assert!(!trace.notes.iter().any(|n| n.message.contains("intact holder capture")));
    let trace = verify_one_file("worker_holder_footprint", source, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
    assert!(
        trace
            .notes
            .iter()
            .any(|n| n.message == "checked helper phase with intact holder capture 0")
    );
    assert!(
        trace.notes.iter().any(
            |n| n.message == "41-byte allocation also observed outside intact holder capture 0"
        )
    );
}

test_verify_one_file! {
    #[test] write_and_read_handles_have_incompatible_roles code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{Holder, BoundedHolder, Incompatible};
        use vstd::rwlock::{ReadHandle, RwLock, RwLockPredicate, WriteHandle};
        verus! {
            struct Any;
            impl RwLockPredicate<u8> for Any {
                open spec fn inv(self, _: u8) -> bool { true }
            }
            proof fn cannot_overlap(tracked mut writer: WriteHandle<'_, u8, Any>,
                                    tracked reader: ReadHandle<'_, u8, Any>)
                ensures writer.rwlock().id() != reader.rwlock().id(),
            {
                writer.distinct_instances(&reader);
            }
            fn two_readers() {
                let lock = RwLock::<u8, Any>::new(7, Ghost(Any));
                let first = lock.acquire_read();
                let second = lock.acquire_read();
                assert(first.instance_id() == second.instance_id());
                first.release_read();
                second.release_read();
                let (value, writer) = lock.acquire_write();
                assert(writer.instance_id() == lock.id() && writer.capacity() == 1);
                writer.release_write(value);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] equal_capacities_do_not_identify_two_semaphores code! {
        use vstd::prelude::*;
        use vstd::resource::holder::Holder;
        use vstd::resource::semaphore::Semaphore;
        verus! {
            fn wrong() {
                let a = Semaphore::new(1);
                let b = Semaphore::new(1);
                let p = a.acquire();
                assert(p.instance_id() == b.id()); // FAILS
                p.release();
            }
        }
    } => Err(e) => assert_one_fails(e)
}
