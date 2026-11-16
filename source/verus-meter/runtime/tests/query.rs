//! Compile and run the public example against a prepared verifier distribution.
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn compile(source: &str, directory: &Path) -> (Output, PathBuf) {
    let verifier = std::env::var_os("VERUS_QUERY_TEST_VERIFIER")
        .expect("set VERUS_QUERY_TEST_VERIFIER to the prepared verus executable");
    let release = std::env::current_exe().unwrap().parent().unwrap().parent().unwrap().to_owned();
    let input = directory.join("query.rs");
    let executable = directory.join(format!("query{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(&input, source).unwrap();
    let mut command = Command::new(verifier);
    command
        .arg(input)
        .arg("--compile")
        .arg("--extern")
        .arg(format!(
            "verus_meter_runtime={}",
            release.join("libverus_meter_runtime.rlib").display()
        ))
        .arg("-L")
        .arg(format!("dependency={}", release.join("deps").display()))
        .arg("-o")
        .arg(&executable);
    if let Some(dependencies) = std::env::var_os("VERUS_QUERY_TEST_DEPS") {
        command.arg("-L").arg(format!("dependency={}", PathBuf::from(dependencies).display()));
    }
    (command.output().unwrap(), executable)
}

fn succeeds(output: &Output) {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "requires built runtime and prepared verifier; see runtime README"]
fn compiled_query_tracks_contract_and_types() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source =
        std::fs::read_to_string(root.join("examples/resource/memory/contracts/runtime_query.rs"))
            .unwrap();
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(&source, directory.path());
    succeeds(&output);
    for (budget, message) in [
        ("1200", "Admitted: allowance 1124, capacity 100"),
        ("1000", "Declined: allowance 1124 exceeds budget 1000"),
    ] {
        let output = Command::new(&executable).arg(budget).output().unwrap();
        succeeds(&output);
        assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), message);
    }
    let output = Command::new(&executable).args(["2000", "200"]).output().unwrap();
    succeeds(&output);
    assert!(String::from_utf8(output.stdout).unwrap().contains("allowance 1224, capacity 200"));
    let (output, executable) =
        compile(&source.replace("1024 + count", "2048 + count"), directory.path());
    succeeds(&output);
    let output = Command::new(executable).arg("3000").output().unwrap();
    succeeds(&output);
    assert!(String::from_utf8(output.stdout).unwrap().contains("allowance 2148"));

    let (output, executable) =
        compile(&source.replace("1024 + count", "1024 + 8 * count"), directory.path());
    succeeds(&output);
    let output = Command::new(executable).arg("2000").output().unwrap();
    succeeds(&output);
    assert!(String::from_utf8(output.stdout).unwrap().contains("allowance 1824"));

    // Verification still constrains execution inputs. A query outside that domain
    // may return a larger allowance, which must remain exact and decline admission.
    let large_source = source
        .replace("count: u16", "count: u64")
        .replace("100u16", "100u64")
        .replace("count must fit u16", "count must fit u64")
        .replace("with_capacity(count as usize)", "with_capacity(100usize)")
        .replace(
            "    resources peak(memory) <= 1024 + count,",
            "    requires count <= 100,\n    resources peak(memory) <= 1024 + 8 * count,",
        );
    let (output, executable) = compile(&large_source, directory.path());
    succeeds(&output);
    let output = Command::new(executable)
        .args(["18446744073709551615", "18446744073709551615"])
        .output()
        .unwrap();
    succeeds(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "Declined: allowance 147573952589676413944 exceeds budget 18446744073709551615"
    );

    for (source, message) in [
        (
            source.replace("    resources peak(memory) <= 1024 + count,", ""),
            "queryable_peak_memory requires resources",
        ),
        (source.replace("peak_memory_bound(count)", "peak_memory_bound(true)"), "mismatched types"),
        (
            source.replace("1024 + count", "peak(allocate)"),
            "runtime peak(helper) queries are unsupported",
        ),
    ] {
        let (output, _) = compile(&source, directory.path());
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "requires built runtime and prepared verifier; see runtime README"]
fn compiled_expressions_helpers_and_model_sizes() {
    let source = r#"
use vstd::prelude::*;
verus_builtin_macros::verus! {
    type Words = [u16; 3];
    type SliceRef<'a> = &'a [u32];
    spec fn element_bytes(count: nat) -> nat {
        let stride = value_size(u32);
        stride * count
    }
    spec fn budget(n: u16, m: u8, large: bool) -> nat {
        let count = n as nat;
        let count = count + 1;
        let extra = if large && n > 0 { element_bytes(count) } else { m as nat };
        1024 + extra + ref_size(SliceRef) + value_size(Vec<u32>)
            + value_size(Words) + value_size(n)
    }
    #[queryable_peak_memory]
    fn queried(n: u16, m: u8, large: bool)
        resources peak(memory) <= budget(n, m, large),
    {}
    #[queryable_peak_memory]
    fn direct(n: u16, m: u8, large: bool)
        resources peak(memory) <= 1072 + if large && n > 0 { 4 * (n + 1) } else { m },
    {}
    #[queryable_peak_memory]
    fn delegated(n: u16, m: u8, large: bool)
        resources peak(memory) <= 1024 + peak(queried(n, m, large)),
    { queried(n, m, large); }
    #[queryable_peak_memory]
    fn controls(a: bool, b: bool, n: u16, m: u8)
        resources peak(memory) <= 128 + if (a == b) || (n <= 2 && !a) { m } else { n },
    {}
}
fn main() {
    assert_eq!(queried::peak_memory_bound(3, 5, true).unwrap().to_u64().unwrap(), 1088);
    assert_eq!(queried::peak_memory_bound(3, 5, false).unwrap().to_u64().unwrap(), 1077);
    assert_eq!(queried::peak_memory_bound(0, 9, true).unwrap().to_u64().unwrap(), 1081);
    assert_eq!(queried::peak_memory_bound(3, 5, true), direct::peak_memory_bound(3, 5, true));
    assert_eq!(queried::peak_memory_bound(0, 9, false), direct::peak_memory_bound(0, 9, false));
    assert_eq!(delegated::peak_memory_bound(3, 5, true).unwrap().to_u64().unwrap(), 2112);
    assert_eq!(controls::peak_memory_bound(true, false, 3, 5).unwrap().to_u64().unwrap(), 131);
    assert_eq!(controls::peak_memory_bound(false, false, 3, 5).unwrap().to_u64().unwrap(), 133);
    assert_eq!(controls::peak_memory_bound(false, true, 2, 5).unwrap().to_u64().unwrap(), 133);
}
"#;
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(source, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    let changed = source.replace("stride * count", "stride * count + 10")
        .replace("1088", "1098")
        .replace("2112", "2122")
        .replace("assert_eq!(queried::peak_memory_bound(3, 5, true), direct::peak_memory_bound(3, 5, true));", "");
    let (output, executable) = compile(&changed, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());

    for (replacement, message) in [
        ("let unused = 1 / 1; stride * count", "unsupported arithmetic operation"),
        ("element_bytes(count)", "recursive spec helpers"),
        ("(stride * count) as u64 as nat", "native casts are unsupported"),
        ("other_module::bytes(count)", "same verus item scope"),
        ("(|n: nat| n)(count)", "higher-order spec applications"),
    ] {
        let (output, _) = compile(&source.replace("stride * count", replacement), directory.path());
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let unchecked =
        source.replace("spec fn element_bytes", "#[verifier::external_body] spec fn element_bytes");
    let (output, _) = compile(&unchecked, directory.path());
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("checked body"));

    let custom_struct =
        source.replace("type Words = [u16; 3];", "struct Words { small: u8, large: u32 }");
    let (output, _) = compile(&custom_struct, directory.path());
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("ValueSize"));
}
