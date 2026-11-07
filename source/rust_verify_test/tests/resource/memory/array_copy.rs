use crate::common::*;
use crate::verify_one_file;

#[test]
fn array_copy_exceeds_the_declared_budget() {
    // Verify the example exactly as written: the original and its copy
    // coexist, but the contract allows room for just one array.
    let err = verify_one_file(
        "array_copy_exceeds_the_declared_budget",
        include_str!("../../../../../examples/resource/memory/expected-failures/array_copy.rs")
            .into(),
        &[],
    )
    .unwrap_err();

    // Acceptance or a different error makes this test fail.
    assert_vir_error_msg(err, "peak 32 bytes exceeds budget 16 bytes");
}
