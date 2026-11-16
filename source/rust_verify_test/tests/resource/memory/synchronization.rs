//! Size queries and fail-closed compiler integration for synchronization contracts.
use super::support::{rejects, verifies};

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
fn runtime_mutex_is_not_accepted_without_lifetime_coverage() {
    rejects(
        "mutex_coverage",
        r#"
        #[verifier::assume(externals_available_without_declaration)]
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(1u64);
        }
    "#,
        "runtime synchronization values before guard cleanup and concurrent lifetime accounting are available",
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
        "runtime synchronization values before guard cleanup and concurrent lifetime accounting are available",
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
