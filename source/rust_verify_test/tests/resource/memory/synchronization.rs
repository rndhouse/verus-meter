//! Size queries and fail-closed compiler integration for synchronization contracts.
use super::support::{rejects, verifies};

mod atomic;
mod helpers;
mod lifetimes;
mod mutex;
mod payload;
mod shared_payloads;

#[test]
fn opaque_sizes_are_source_model_values() {
    verifies(
        "synchronization_sizes",
        r#"
        fn sizes() resources peak(memory) <= 0 {
            assert(value_size(std::sync::Mutex<u64>) == 17);
            assert(value_size(std::sync::MutexGuard<'static, u64>) == 8);
            assert(value_size(Result<u8, u64>) == 9);
        }
    "#,
    );
}

#[test]
fn tracked_guards_are_not_runtime_memory_roots() {
    verifies(
        "tracked_guard",
        r#"
        fn f(tracked guard: std::sync::MutexGuard<'static, u64>)
            resources peak(memory) <= 0 {}
    "#,
    );
}

#[test]
fn native_mutex_surface_keeps_acquisition_outcomes_visible() {
    verifies(
        "mutex_native_surface",
        r#"
        fn f() {
            let mutex = std::sync::Mutex::new(1u64);
            match mutex.try_lock() {
                Ok(mut guard) => {
                    let view = &*guard;
                    let value = *view;
                    *guard = value;
                    drop(guard);
                },
                Err(std::sync::TryLockError::WouldBlock) => {},
                Err(std::sync::TryLockError::Poisoned(poison)) => { drop(poison); },
            };
        }
    "#,
    );
}

#[test]
fn native_specifications_do_not_assume_acquisition_succeeds() {
    rejects(
        "mutex_no_assumed_success",
        r#"
        fn f(mutex: &std::sync::Mutex<u64>) {
            let result = mutex.try_lock();
            assert(result matches Ok(_));
        }
    "#,
        "assertion failed",
    );
}

#[test]
fn lifetime_checks_cannot_be_bypassed_for_runtime_synchronization() {
    let error = crate::verify_one_file(
        "mutex_no_lifetime",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f(m: &std::sync::Mutex<u64>) resources peak(memory) <= 1000 {}
        }
    "#
        .into(),
        &["--no-lifetime"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error,
        "runtime synchronization memory analysis requires lifetime checking",
    );
}

#[test]
fn user_names_do_not_receive_standard_mutex_layouts() {
    verifies(
        "user_mutex_layout",
        r#"
        struct Mutex { byte: u8 }
        fn f() resources peak(memory) <= 1 {
            assert(value_size(Mutex) == 1);
            let m = Mutex { byte: 7 };
        }
    "#,
    );
}

#[test]
fn containing_a_guard_does_not_bypass_the_cleanup_boundary() {
    rejects(
        "guard_field_coverage",
        r#"
        struct Wrapper { guard: std::sync::MutexGuard<'static, u64> }
        fn f(w: Wrapper) resources peak(memory) <= 1000 {}
    "#,
        "before concurrent lifetime accounting is available",
    );
}

#[test]
fn opaque_guard_specification_preserves_rust_send_restriction() {
    let err = crate::verify_one_file(
        "guard_send",
        r#"
        use vstd::prelude::*;
        verus! {
            fn requires_send<T: Send>(value: T) {}
            fn invalid(guard: std::sync::MutexGuard<'static, u64>) {
                requires_send(guard);
            }
        }
    "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_rust_error_msg(err, "cannot be sent between threads safely");
}
