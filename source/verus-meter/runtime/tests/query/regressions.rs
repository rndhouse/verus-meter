//! End-to-end checks at the boundary between verification and executable queries.
use super::{compile, succeeds};
use std::process::Command;

#[test]
#[ignore = "requires prepared verifier and runtime bundle; see runtime README"]
fn numeric_inputs_and_queries_outside_preconditions() {
    let source = r#"
use vstd::prelude::*;
use verus_meter_runtime::NativeRangeError;
verus! {
    spec fn weighted(a: u8, b: u16, c: u32, d: u64, e: usize) -> nat {
        a as nat + 2 * (b as nat) + 3 * (c as nat) + 4 * (d as nat) + 5 * (e as nat)
    }
    #[queryable_peak_memory]
    fn mixed(a: u8, b: u16, c: u32, d: u64, e: usize, active: bool)
        requires c <= 100, d <= 100, e <= 100,
        resources peak(memory) <= 1024 + if active { weighted(a, b, c, d, e) } else { 0 },
    {}
    spec fn cancelled_square(n: u64) -> nat {
        let square = (n as nat) * (n as nat);
        1024 + square * 0
    }
    #[queryable_peak_memory]
    fn intermediate(n: u64) resources peak(memory) <= cancelled_square(n) {}
    #[queryable_peak_memory]
    fn restricted(n: u64)
        requires n >= 1024,
        resources peak(memory) <= n,
    {}
    fn caller() { restricted(1024); }
    #[queryable_peak_memory]
    fn empty() resources peak(memory) <= 0 {}
}
fn main() {
    // These decimal expectations are independent of the generated representation.
    for (a, b, c, d, e, expected) in [
        (0, 0, 0, 0, 0, "1024"),
        (u8::MAX, 0, 0, 0, 0, "1279"),
        (0, u16::MAX, 0, 0, 0, "132094"),
        (0, 0, u32::MAX, 0, 0, "12884902909"),
        (0, 0, 0, u64::MAX, 0, "73786976294838207484"),
        (1, 2, 3, 4, 5, "1079"),
    ] {
        assert_eq!(mixed::peak_memory_bound(a, b, c, d, e, true).unwrap().to_string(), expected);
    }
    // The source memory model is 64-bit; exercise the native input conversion too.
    assert_eq!(usize::BITS, 64);
    let huge = mixed::peak_memory_bound(0, 0, 0, 0, usize::MAX, true).unwrap();
    assert_eq!(huge.to_string(), "92233720368547759099");
    assert_eq!(huge.to_u64(), Err(NativeRangeError));
    assert!(!huge.fits_within(u64::MAX));
    assert_eq!(mixed::peak_memory_bound(1, 2, 3, 4, 5, false).unwrap().to_u64(), Ok(1024));
    assert_eq!(intermediate::peak_memory_bound(u64::MAX).unwrap().to_u64(), Ok(1024));
    assert!(empty::peak_memory_bound().unwrap().fits_within(0));

    let equality = restricted::peak_memory_bound(1024).unwrap();
    assert!(equality.fits_within(1024));
    assert!(!equality.fits_within(1023));
    // Querying accepts this input, even though calling restricted(0) is invalid.
    let outside = restricted::peak_memory_bound(0).unwrap();
    assert_eq!(outside.to_u64(), Ok(0));
    assert!(outside.fits_within(0));
}
"#;
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(source, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());

    let (output, _) =
        compile(&source.replace("restricted(1024);", "restricted(0);"), directory.path());
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("precondition not satisfied"));
}

#[test]
#[ignore = "requires prepared verifier and runtime bundle; see runtime README"]
fn helper_substitution_and_typed_local_sizes() {
    let source = r#"
use vstd::prelude::*;
verus! {
    spec fn pair(left: nat, right: nat) -> nat {
        let saved = left;
        let left = right + 1;
        saved * 10 + left
    }
    spec fn remapped(left: u16, right: u16) -> nat {
        pair(right as nat, left as nat) + pair(left as nat, left as nat)
    }
    #[queryable_peak_memory]
    fn remap(left: u16, right: u16)
        resources peak(memory) <= 1024 + remapped(left, right),
    {}
    spec fn local_sizes(n: u16) -> nat {
        let copied: u16 = n;
        value_size(copied) + value_size(Option<u64>) + value_size(Box<[u8]>)
            + ref_size(&mut u32) + value_size(())
    }
    #[queryable_peak_memory]
    fn sizes(n: u16) resources peak(memory) <= 1024 + local_sizes(n) {}
}
fn main() {
    assert_eq!(remap::peak_memory_bound(2, 7).unwrap().to_u64(), Ok(1120));
    assert_eq!(remap::peak_memory_bound(7, 2).unwrap().to_u64(), Ok(1130));
    assert_eq!(sizes::peak_memory_bound(0).unwrap().to_u64(), Ok(1059));
}
"#;
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(source, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    let changed = source
        .replace("saved * 10", "saved * 100")
        .replace("Ok(1120)", "Ok(1930)")
        .replace("Ok(1130)", "Ok(1940)");
    let (output, executable) = compile(&changed, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
}

#[test]
#[ignore = "requires prepared verifier and runtime bundle; see runtime README"]
fn query_attribute_preserves_resource_verification_failures() {
    let source = r#"
use vstd::prelude::*;
verus! {
    #[queryable_peak_memory]
    fn checked() resources peak(memory) <= 32 {
        let buffer = [0u8; 32];
    }
}
fn main() { assert_eq!(checked::peak_memory_bound().unwrap().to_u64(), Ok(32)); }
"#;
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(source, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    // The same body exceeds its allowance with or without query generation.
    let short = source.replace("peak(memory) <= 32", "peak(memory) <= 31");
    for annotated in [true, false] {
        let short = if annotated {
            short.clone()
        } else {
            short
                .replace("#[queryable_peak_memory]", "")
                .replace("assert_eq!(checked::peak_memory_bound().unwrap().to_u64(), Ok(32));", "")
        };
        let (output, _) = compile(&short, directory.path());
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("memory budget exceeded"));
    }
}

#[test]
#[ignore = "requires prepared verifier and runtime bundle; see runtime README"]
fn unsupported_nested_dependencies_fail_before_execution() {
    let directory = tempfile::tempdir().unwrap();
    for (dependencies, allowance, diagnostic) in [
        (
            "spec fn inner(n: nat) -> nat { if n == 0 { n / 2 } else { n } } spec fn outer(n: nat) -> nat { 1024 + inner(n) }",
            "outer(n as nat)",
            "unsupported arithmetic operation",
        ),
        (
            "fn missing(n: u16) {}",
            "peak(missing(n))",
            "runtime peak target requires a resource contract",
        ),
        (
            "spec fn inner(n: nat) -> nat { let mut copy = n; copy } spec fn outer(n: nat) -> nat { 1024 + inner(n) }",
            "outer(n as nat)",
            "runtime helper bindings must be immutable",
        ),
    ] {
        let source = format!(
            r#"use vstd::prelude::*;
verus! {{
    {dependencies}
    #[queryable_peak_memory]
    fn queried(n: u16) resources peak(memory) <= {allowance} {{}}
}}
fn main() {{}}
"#
        );
        let (output, _) = compile(&source, directory.path());
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(diagnostic),
            "{dependencies}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
