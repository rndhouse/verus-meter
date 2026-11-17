//! Native thread/shared-storage surface and executable compiler evidence.
use super::support::{exact_peak, rejects, verifies};

#[test]
fn logical_clone_erasure_cannot_shorten_an_unsupported_borrowing_comparison() {
    rejects(
        "shared_comparison_temporary_lifetime",
        r#"
        fn f() resources peak(memory) <= 10000 {
            let first = std::sync::Arc::new(7u64);
            let second = std::sync::Arc::new(7u64);
            let equal = first.clone() == ({
                drop(first);
                let scratch = [0u8;128];
                second
            }).clone();
        }
    "#,
        "borrowed temporary",
    );
}

#[test]
fn section_receiver_temporaries_keep_their_own_charges_during_parent_cleanup() {
    exact_peak(
        "section_receiver_temporary_parent_frame",
        r#"
        fn f() -> Box<[u8;64]> resources peak(memory) <= BUDGET {
            let output = Box::new([0u8;64]);
            let root = std::sync::Arc::new(7u64);
            resources peak(memory) <= 40 {
                drop(std::sync::Arc::new(9u64).clone())
            }
            drop(root);
            let scratch = [0u8;128];
            output
        }
    "#,
        200,
    );
}

#[test]
fn canonical_shared_payloads_keep_incoming_lifetime_profiles() {
    exact_peak(
        "native_shared_input_lifetime",
        r#"
        fn consume(input: Box<[u8;64]>) resources peak(memory) <= 128 {
            let root = std::sync::Arc::new(input);
            let copy = root.clone();
            drop(root);
            { let scratch = [0u8;32]; }
            drop(copy);
            let scratch = [0u8;128];
        }
        fn f() resources peak(memory) <= BUDGET {
            let input = Box::new([0u8;64]);
            consume(input);
        }
    "#,
        128,
    );
    exact_peak(
        "native_nested_shared_input_lifetime",
        r#"
        fn consume(input: Box<[u8;64]>) resources peak(memory) <= 128 {
            let inner = std::sync::Arc::new(input);
            let outer = std::sync::Arc::new(inner);
            drop(outer);
            let scratch = [0u8;128];
        }
        fn f() resources peak(memory) <= BUDGET {
            let input = Box::new([0u8;64]);
            consume(input);
        }
    "#,
        128,
    );
    exact_peak(
        "native_boxed_shared_input_lifetime",
        r#"
        fn consume(input: Box<[u8;64]>) resources peak(memory) <= 128 {
            let wrapped = Box::new(std::sync::Arc::new(input));
            drop(wrapped);
            let scratch = [0u8;128];
        }
        fn f() resources peak(memory) <= BUDGET {
            let input = Box::new([0u8;64]);
            consume(input);
        }
    "#,
        128,
    );
}

#[test]
fn unknown_alias_inputs_and_reference_populations_require_descriptors() {
    rejects(
        "native_unmodelled_shared_input",
        r#"
        fn f(input: std::sync::Arc<u64>) resources peak(memory) <= 100000 {
            drop(input);
        }
    "#,
        "shared input roots without a checked alias descriptor",
    );
    rejects(
        "native_unmodelled_nested_shared_input",
        r#"
        fn f(input: Vec<Vec<std::sync::Arc<u64>>>) resources peak(memory) <= 100000 {
            drop(input);
        }
    "#,
        "shared input roots without a checked alias descriptor",
    );
    rejects(
        "native_unmodelled_shared_population",
        r#"
        fn f() resources peak(memory) <= 100000 {
            let root = std::sync::Arc::new(7u64);
            let mut aliases = Vec::with_capacity(1);
            aliases.push(root.clone());
            drop(aliases);
            drop(root);
        }
    "#,
        "without an identity summary",
    );
}

#[test]
fn native_shared_borrows_and_consuming_temporary_drops_are_accounted() {
    exact_peak(
        "native_explicit_shared_borrow",
        r#"
        use std::ops::Deref;
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let borrowed = root.deref();
            let value = *borrowed;
        }
    "#,
        48,
    );
    exact_peak(
        "native_consumed_clone",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            drop(root.clone());
        }
    "#,
        40,
    );
    exact_peak(
        "native_consumed_temporary_clone",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            drop(std::sync::Arc::new(Box::new([0u8;64])).clone());
            let scratch = [0u8;64];
        }
    "#,
        104,
    );
}

#[test]
fn per_iteration_strong_aliases_do_not_accumulate_historical_clones() {
    exact_peak(
        "symbolic_local_strong_aliases",
        r#"
        fn f(n: u16) resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let mut index = 0u16;
            while index < n
                invariant index <= n,
                decreases n - index,
            {
                let copy = root.clone();
                drop(copy);
                index += 1;
            }
            drop(root);
        }
    "#,
        44,
    );
}

#[test]
fn borrowed_clone_receivers_retain_storage_through_all_statement_operands() {
    exact_peak(
        "clone_receiver_statement_overlap",
        r#"
        struct Pair { left: std::sync::Arc<u64>, right: Box<[u8;64]> }
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let pair = Pair { left: root.clone().clone(), right: Box::new([0u8;64]) };
            drop(pair);
        }
    "#,
        120,
    );
    exact_peak(
        "clone_receiver_nested_block_overlap",
        r#"
        struct Pair { left: std::sync::Arc<u64>, right: Box<[u8;1]> }
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let pair = Pair {
                left: root.clone().clone(),
                right: {
                    let local = Box::new([0u8;64]);
                    drop(local);
                    Box::new([0u8;1])
                },
            };
            drop(pair);
        }
    "#,
        128,
    );
    exact_peak(
        "clone_receiver_statement_reuse",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let copy = root.clone().clone();
            drop(root);
            drop(copy);
            let scratch = [0u8;64];
        }
    "#,
        64,
    );
}

#[test]
fn native_strong_aliases_charge_backing_once_and_release_it_at_the_last_drop() {
    exact_peak(
        "native_strong_lifetimes",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(Box::new([0u8;64]));
            let copy = root.clone();
            drop(root);
            let scratch = [0u8;128];
            drop(copy);
        }
    "#,
        224,
    );
    exact_peak(
        "native_final_strong_drop",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(7u64);
            let copy = root.clone();
            drop(root);
            drop(copy);
            let scratch = [0u8;64];
        }
    "#,
        64,
    );
}

#[test]
fn shared_payload_reads_and_captured_aliases_preserve_canonical_storage() {
    exact_peak(
        "native_shared_read",
        r#"
        struct State { count: u64, buffer: Box<[u8;64]> }
        fn f() resources peak(memory) <= BUDGET {
            let root = std::sync::Arc::new(State { count: 7u64, buffer: Box::new([0u8;64]) });
            let value = root.count;
            let copy = root.clone();
            let closure = move || { drop(copy); };
            drop(root);
            let scratch = [0u8;128];
            drop(closure);
        }
    "#,
        240,
    );
}

#[test]
fn ownership_forests_preserve_reference_identity_and_alias_multiplicity() {
    verifies(
        "ownership_reference_transport",
        r#"
        use vstd::std_specs::resource::memory::{forest::*, references::*};
        proof fn transport(identity: Seq<int>, parent: Seq<int>) {
            let shared = Reference::Shared(identity);
            let worker = Reference::Worker(identity);
            let one = Seq::<Record>::empty().push(shared_reference(Seq::empty(), identity));
            let another = Seq::<Record>::empty().push(worker_reference(Seq::empty(), identity));
            reveal_with_fuel(reference_count, 2);
            assert(reference_count(one, shared) == 1);
            assert(reference_count(one, worker) == 0);
            assert(reference_count(another, worker) == 1);
            reference_count_add(one, one, shared);
            assert(reference_count(one + one, shared) == 2);
            reference_count_add(one, another, shared);
            reference_count_add(one, another, worker);
            reference_count_prefix(one + another, parent, shared);
            reference_count_prefix(one + another, parent, worker);
            assert(reference_count(prefix(one + another, parent), shared) == 1);
            assert(reference_count(prefix(one + another, parent), worker) == 1);
            reference_count_partition(prefix(one + another, parent), parent, shared);
            reference_count_partition(prefix(one + another, parent), parent, worker);
        }
    "#,
    );
}

#[test]
fn worker_forests_preserve_symbolic_family_membership_and_distinct_occurrences() {
    verifies(
        "worker_family_transport",
        r#"
        use vstd::std_specs::resource::memory::{forest::*, references::*};
        proof fn families(family: Seq<int>, index: int, next: int, owner: Seq<int>)
            requires index != next,
        {
            let a = family.push(index);
            let b = family.push(next);
            let first = Seq::<Record>::empty().push(worker_reference(Seq::empty(), a));
            let second = Seq::<Record>::empty().push(worker_reference(Seq::empty(), b));
            let target = Reference::WorkerFamily(family);
            reveal_with_fuel(reference_count, 2);
            assert(family.is_prefix_of(a));
            assert(family.is_prefix_of(b));
            assert(a != b) by { assert(a.last() != b.last()); }
            assert(reference_count(first, Reference::Worker(b)) == 0);
            assert(reference_count(first, target) == 1);
            assert(reference_count(second, target) == 1);
            reference_count_add(first, second, target);
            assert(reference_count(first + second, target) == 2);
            reference_count_prefix(first + second, owner, target);
            reference_count_partition(prefix(first + second, owner), owner, target);
            assert(reference_count(prefix(first + second, owner), target) == 2);
        }
    "#,
    );
}

#[test]
fn symbolic_reference_populations_compose_without_repeating_worker_identities() {
    verifies(
        "symbolic_reference_population",
        r#"
        use vstd::std_specs::resource::memory::{blocks::*, forest::*, ranges::*, references::*};
        proof fn populations(count: nat, family: Seq<int>, root: Seq<int>) {
            let target = Reference::WorkerFamily(family);
            let builder = |index: int| Seq::<Record>::empty().push(
                worker_reference(seq![0], family.push(index)));
            assert forall|index: int| 0 <= index < count implies
                reference_count(#[trigger] builder(index), target) == 1 by
            {
                reveal_with_fuel(reference_count, 2);
                assert(family.is_prefix_of(family.push(index)));
            }
            reference_count_generate(builder, 1, count as int, 0, target);
            generated_reference_count_uniform(builder, count as int, target, 1);
            assert(reference_count(generate_children(builder, 1, count as int, 0), target) == count);

            let alias = Seq::<Record>::empty().push(shared_reference(Seq::empty(), root));
            reveal_with_fuel(reference_count, 2);
            assert(reference_count(alias, Reference::Shared(root)) == 1);
            reference_count_repeat(alias, 0, count as int, Reference::Shared(root));
            assert(reference_count(repeat(alias, 0, count as int), Reference::Shared(root)) == count);
            reference_count_partition(repeat(alias, 0, count as int), seq![0], Reference::Shared(root));
        }
    "#,
    );
}

#[test]
fn move_closure_retains_actual_allocations_until_its_drop() {
    let code = r#"
        fn f() resources peak(memory) <= BUDGET {
            let owner = Box::new([0u8;64]);
            let closure = move || {
                let latent = Box::new([0u8;8192]);
                drop(owner); drop(latent);
            };
            let scratch = [0u8;128];
            drop(closure);
        }
    "#;
    exact_peak("moved_capture", code, 200);
    rejects(
        "edited_capture_allocation",
        &code.replace("BUDGET", "200").replace("[0u8;64]", "[0u8;96]"),
        "memory budget exceeded",
    );
}

#[test]
fn invoking_a_latent_body_requires_a_checked_memory_effect() {
    rejects(
        "invoked_capture_body",
        r#"
        fn f() resources peak(memory) <= 200 {
            let owner = Box::new([0u8;64]);
            let closure = move || {
                let scratch = Box::new([0u8;8192]);
                drop(owner);
                drop(scratch);
            };
            closure();
        }
    "#,
        "calls with generic, dynamic, or unsupported targets",
    );
}

#[test]
fn simultaneous_owned_and_copied_captures_keep_every_charge() {
    exact_peak(
        "simultaneous_captures",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let first = Box::new([0u8;64]);
            let second = Box::new([0u8;96]);
            let count = 7u16;
            let closure = move || {
                drop(first);
                drop(second);
                count
            };
            let scratch = [0u8;128];
            drop(closure);
        }
    "#,
        308,
    );
}

#[test]
fn copy_closures_keep_the_source_and_charge_the_drop_argument() {
    exact_peak(
        "copied_capture",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let value = 7u64;
            let closure = move || value;
            drop(closure);
        }
    "#,
        24,
    );
}

#[test]
fn erased_noncopy_proof_capture_cannot_hide_executable_closure_copies() {
    exact_peak(
        "erased_capture_copy",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let value = 7u64;
            let tracked token = Box::new(9u64);
            let closure = move || {
                proof { let tracked consumed = token; }
                value
            };
            drop(closure);
        }
    "#,
        24,
    );
}

#[test]
fn executable_copy_decisions_propagate_through_nested_capture_fields() {
    exact_peak(
        "nested_erased_capture_copy",
        r#"
        fn f() resources peak(memory) <= BUDGET {
            let value = 7u64;
            let tracked token = Box::new(9u64);
            let first = move || {
                proof { let tracked consumed = token; }
                value
            };
            let second = move || first();
            drop(second);
        }
    "#,
        32,
    );
}

#[test]
fn partial_capture_transfers_only_the_selected_child_owner() {
    exact_peak(
        "partial_capture",
        r#"
        struct State { left: Box<[u8;64]>, right: Box<[u8;128]> }
        fn f() resources peak(memory) <= BUDGET {
            let state = State { left: Box::new([0u8;64]), right: Box::new([0u8;128]) };
            let closure = move || { drop(state.left); };
            drop(state.right);
            let scratch = [0u8;128];
            drop(closure);
        }
    "#,
        216,
    );
}

#[test]
fn proof_only_capture_fields_occupy_no_executable_storage() {
    verifies(
        "proof_capture_storage",
        r#"
        fn f() resources peak(memory) <= 0 {
            let ghost value = 7int;
            let tracked token = 9u64;
            let closure = move || {
                proof { assert(value == 7); assert(token == 9); }
                0u8
            };
            drop(closure);
        }
    "#,
    );
}

#[test]
fn shared_and_worker_handles_have_source_sizes() {
    verifies(
        "concurrent_sizes",
        r#"
        fn sizes() resources peak(memory) <= 0 {
            assert(value_size(std::sync::Arc<u64>) == 8);
            assert(value_size(std::sync::Arc<std::sync::Mutex<u64>>) == 8);
            assert(value_size(std::thread::JoinHandle<u64>) == 8);
            assert(value_size(vstd::thread::JoinHandle<u64>) == 8);
            assert(value_size(std::thread::Result<u64>) == 17);
            assert(value_size(Ghost<std::sync::Arc<u64>>) == 0);
            assert(value_size(Tracked<u64>) == 0);
        }
    "#,
    );
}

#[test]
fn logical_identity_erasure_preserves_only_executable_arc_clones() {
    let result = crate::verify_one_file(
        "arc_clone_erasure",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let root = std::sync::Arc::new(7u64);
                proof { let ghost_copy = root.clone(); }
                let copy = root.clone();
                drop(copy);
                drop(root);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap();
    assert_eq!(
        result
            .notes
            .iter()
            .filter(|note| note.message.contains("memory executable effect: ArcClone"))
            .count(),
        1
    );
}

#[test]
fn native_threads_retain_functional_worker_postconditions() {
    verifies(
        "native_thread_postconditions",
        r#"
        fn f() {
            let value = 7u64;
            let handle = std::thread::spawn(move || {
                ensures(|result: u64| result == value);
                value
            });
            match handle.join() {
                Ok(result) => { assert(result == value); },
                Err(error) => { drop(error); },
            }
        }
    "#,
    );
}

#[test]
fn join_success_is_not_assumed_from_functional_specifications() {
    rejects(
        "native_join_no_assumed_success",
        r#"
        fn f() {
            let handle = std::thread::spawn(move || 7u64);
            let result = handle.join();
            assert(result matches Ok(_));
        }
    "#,
        "assertion failed",
    );
}

#[test]
fn worker_capture_bridge_runs_before_the_global_memory_gate() {
    rejects(
        "worker_capture_bridge",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let shared = std::sync::Arc::new(7u64);
            let copy = shared.clone();
            let handle = std::thread::spawn(move || *copy);
            let result = handle.join();
            drop(result);
        }
    "#,
        "before concurrent lifetime accounting is available",
    );
}

#[test]
fn proof_only_uses_do_not_make_runtime_worker_captures() {
    let error = crate::verify_one_file(
        "worker_proof_capture_bridge",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1000 {
            let value = 7u64;
            let tracked token = 8u64;
            let handle = vstd::thread::spawn(move || {
                proof { assert(value == 7); assert(token == 8); }
                0u8
            });
            let result = handle.join();
            drop(result);
        }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert!(error.notes.iter().any(|note| {
        note.message.contains("memory closure captures: 0 executable fields, 0 inline source bytes")
    }));
}

#[test]
fn worker_dependencies_participate_in_recursion_checks() {
    rejects(
        "worker_recursive_dependency",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let handle = std::thread::spawn(move || f());
            let result = handle.join();
            drop(result);
        }
    "#,
        "recursive memory contracts",
    );
}

#[test]
fn nested_worker_dependencies_participate_in_recursion_checks() {
    rejects(
        "nested_worker_recursive_dependency",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let handle = vstd::thread::spawn(move || {
                let child = std::thread::spawn(move || f());
                let result = child.join();
                drop(result);
            });
            let result = handle.join();
            drop(result);
        }
    "#,
        "recursive memory contracts",
    );
}

#[test]
fn moved_owners_and_copied_scalars_have_executable_capture_storage() {
    let error = crate::verify_one_file(
        "worker_mixed_capture_storage",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let owner = Box::new([0u8; 16]);
                let shared = std::sync::Arc::new(7u64);
                let count = 2u16;
                let tracked token = 8u64;
                let handle = std::thread::spawn(move || {
                    proof { assert(token == 8); }
                    drop(owner);
                    *shared + count as u64
                });
                let result = handle.join();
                drop(result);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert!(error.notes.iter().any(|note| {
        note.message
            .contains("memory closure captures: 3 executable fields, 18 inline source bytes")
    }));
}

#[test]
fn native_spawn_preserves_rust_send_checks() {
    let error = crate::verify_one_file(
        "worker_requires_send",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f() {
            let value = std::rc::Rc::new(7u64);
            let handle = std::thread::spawn(move || *value);
            let result = handle.join();
            drop(result);
        }
        }
    "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_rust_error_msg(error, "cannot be sent between threads safely");
}

#[test]
fn nested_logical_identity_clones_preserve_every_executable_operation() {
    let result = crate::verify_one_file(
        "nested_arc_clone_erasure",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let root = std::sync::Arc::new(7u64);
                let copy = root.clone().clone();
                drop(copy);
                drop(root);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap();
    assert_eq!(
        result
            .notes
            .iter()
            .filter(|note| { note.message.contains("memory executable effect: ArcClone") })
            .count(),
        2,
    );
}
