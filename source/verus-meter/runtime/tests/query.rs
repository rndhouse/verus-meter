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

    for (source, message) in [
        (
            source.replace("    resources peak(memory) <= 1024 + count,", ""),
            "queryable_peak_memory requires resources",
        ),
        (source.replace("peak_memory_bound(count)", "peak_memory_bound(true)"), "mismatched types"),
        (source.replace("1024 + count", "value_size(u16)"), "currently supports constants"),
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
