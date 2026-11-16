//! Compile and run the public example against a prepared verifier distribution.
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn compile(source: &str, directory: &Path) -> (Output, PathBuf) {
    let verifier = std::env::var_os("VERUS_QUERY_TEST_VERIFIER")
        .expect("set VERUS_QUERY_TEST_VERIFIER to the prepared verus executable");
    let input = directory.join("query.rs");
    let executable = directory.join(format!("query{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(&input, source).unwrap();
    let mut command = Command::new(verifier);
    command.arg(input).arg("--compile").arg("-o").arg(&executable);
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

#[test]
#[ignore = "requires prepared verifier; see runtime README"]
fn interface_configuration_visibility_and_diagnostics() {
    let lint_source = r#"#![deny(non_snake_case, missing_docs)]
#![forbid(unused_imports)]
//! Documented query client.
use vstd::prelude::*;
verus! {
    /// Return a value within the declared allowance.
    #[cfg_attr(all(), allow(non_snake_case))]
    #[queryable_peak_memory]
    pub fn CamelCase(n: u16) -> u16 resources peak(memory) <= 1024 + n { n }
}
fn main() {
    assert_eq!(CamelCase(3), 3);
    assert_eq!(CamelCase::peak_memory_bound(3).unwrap().to_u64().unwrap(), 1027);
}
"#;
    let lint_directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(lint_source, lint_directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    let source = r#"
use vstd::prelude::*;
mod outer {
    use super::*;
    verus_builtin_macros::verus! {
        pub mod inner {
            #[queryable_peak_memory]
            pub(super) fn chosen(__VERUS_QUERY_EXPRESSION: u16, unused: bool)
                resources peak(memory) <= 1024 + __VERUS_QUERY_EXPRESSION,
            {
                resources peak(memory) <= 256 { let scratch = [0u8; 8]; }
                assert(peak(memory) <= 512);
            }
        }
        #[cfg(any())]
        #[queryable_peak_memory]
        fn disabled<T>(unsupported: T) {}
        #[cfg_attr(all(), cfg(any()), deprecated)]
        #[queryable_peak_memory]
        fn also_disabled<T>(unsupported: T) {}
        #[cfg(any())]
        type available = u8;
        #[queryable_peak_memory]
        pub fn available(n: u16) resources peak(memory) <= 1024 + n {}
        #[queryable_peak_memory]
        fn private(n: u16) resources peak(memory) <= 1024 + n {}
        #[test]
        #[queryable_peak_memory]
        fn test_only() resources peak(memory) <= 1024 {}
        spec fn r#budget(r#count: u16) -> nat { 1024 + count as nat }
        #[queryable_peak_memory]
        pub fn r#type(r#input: u16) -> u16
            resources peak(memory) <= budget(input),
        { input }
    }
    pub fn test() {
        inner::chosen(9, false);
        assert_eq!(inner::chosen::peak_memory_bound(9, false).unwrap().to_u64().unwrap(), 1033);
        available(3);
        assert_eq!(available::peak_memory_bound(3).unwrap().to_u64().unwrap(), 1027);
        assert_eq!(private::peak_memory_bound(4).unwrap().to_u64().unwrap(), 1028);
        assert_eq!(r#type(5), 5);
        assert_eq!(r#type::peak_memory_bound(5).unwrap().to_u64().unwrap(), 1029);
    }
}
fn main() { outer::test(); }
"#;
    let directory = tempfile::tempdir().unwrap();
    let (output, executable) = compile(source, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    let wider = source
        .replace("fn available(n: u16)", "fn available(n: u32)")
        .replace("available::peak_memory_bound(3)", "available::peak_memory_bound(3u32)");
    let (output, executable) = compile(&wider, directory.path());
    succeeds(&output);
    succeeds(&Command::new(executable).output().unwrap());
    let (output, _) = compile(
        &wider.replace("peak_memory_bound(3u32)", "peak_memory_bound(3u16)"),
        directory.path(),
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("mismatched types"));
    for (access, message) in [
        ("outer::private::peak_memory_bound(4)", "private"),
        ("outer::inner::chosen::peak_memory_bound(4, true)", "private"),
        ("outer::available::peak_memory_bound(true)", "mismatched types"),
        ("outer::test_only::peak_memory_bound()", "could not find"),
    ] {
        let modified = source
            .replace("fn main() { outer::test(); }", &format!("fn main() {{ let _ = {access}; }}"));
        let (output, _) = compile(&modified, directory.path());
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    for (declaration, message) in [
        ("#[queryable_peak_memory] fn f(n: u16) {}", "requires resources"),
        (
            "#[queryable_peak_memory] #[queryable_peak_memory] fn f(n: u16) resources peak(memory) <= 1024 {}",
            "expected one",
        ),
        (
            "type f = u16; #[queryable_peak_memory] fn f(n: u16) resources peak(memory) <= 1024 {}",
            "query namespace is already occupied",
        ),
        (
            "#[queryable_peak_memory] fn f<T>(n: T) resources peak(memory) <= 1024 {}",
            "safe nongeneric exec free function",
        ),
        ("struct S {} impl S { #[queryable_peak_memory] fn f() {} }", "free functions only"),
        ("trait T { #[queryable_peak_memory] fn f(); }", "free functions only"),
        ("#[queryable_peak_memory] struct S {}", "on a free function"),
        (
            "#[cfg_attr(all(), queryable_peak_memory)] fn f(n: u16) resources peak(memory) <= 1024 {}",
            "directly on the function",
        ),
        (
            "#[cfg(all())] spec fn budget(n: nat) -> nat { 1024 + n } #[queryable_peak_memory] fn f(n: u16) resources peak(memory) <= budget(n as nat) {}",
            "cfg attributes are unsupported",
        ),
    ] {
        let source = format!(
            "use vstd::prelude::*; verus_builtin_macros::verus! {{ {declaration} }} fn main() {{}}"
        );
        let (output, _) = compile(&source, directory.path());
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{declaration}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "requires runtime preparation and release tools; see runtime README"]
fn standalone_bundle_is_relocatable_and_refreshable() {
    let verifier = PathBuf::from(std::env::var_os("VERUS_QUERY_TEST_VERIFIER").unwrap());
    let artifacts = verifier.parent().unwrap();
    let temporary = tempfile::tempdir().unwrap();
    let solver = PathBuf::from(std::env::var_os("VERUS_Z3_PATH").expect("set VERUS_Z3_PATH"));
    std::fs::copy(solver, temporary.path().join(format!("z3{}", std::env::consts::EXE_SUFFIX)))
        .unwrap();
    let distribution = temporary.path().join("distribution");
    succeeds(
        &Command::new(artifacts.join(format!("create-release{}", std::env::consts::EXE_SUFFIX)))
            .current_dir(temporary.path())
            .arg("--build-dir")
            .arg(artifacts)
            .arg("--output-dir")
            .arg(&distribution)
            .output()
            .unwrap(),
    );
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../examples/resource/memory/contracts/runtime_query.rs");
    let executable = temporary.path().join(format!("application{}", std::env::consts::EXE_SUFFIX));
    let relocated_verifier = distribution.join(verifier.file_name().unwrap());
    let run_compiler = |source: &Path| {
        Command::new(&relocated_verifier)
            .arg(source)
            .arg("--compile")
            .arg("-o")
            .arg(&executable)
            .env("VERUS_Z3_PATH", distribution.join(format!("z3{}", std::env::consts::EXE_SUFFIX)))
            .output()
            .unwrap()
    };
    // No extern or dependency-search flags: every library comes from this copy.
    succeeds(&run_compiler(&source));
    let output = Command::new(&executable).arg("1200").output().unwrap();
    succeeds(&output);
    assert!(String::from_utf8(output.stdout).unwrap().contains("Admitted: allowance 1124"));

    let stale = distribution.join("resource-runtime/deps/stale.rlib");
    std::fs::write(&stale, "stale dependency").unwrap();
    succeeds(
        &Command::new(
            artifacts.join(format!("prepare-resource-runtime{}", std::env::consts::EXE_SUFFIX)),
        )
        .arg(&distribution)
        .output()
        .unwrap(),
    );
    assert!(!stale.exists());
    succeeds(&run_compiler(&source));
    // Older distributions remain usable for programs without queries.
    std::fs::remove_dir_all(distribution.join("resource-runtime")).unwrap();
    let plain = temporary.path().join("plain.rs");
    std::fs::write(&plain, "use vstd::prelude::*; verus! { fn main() {} }\n").unwrap();
    succeeds(&run_compiler(&plain));
}

#[test]
#[ignore = "requires cargo-verus and prepared verifier; see runtime README"]
fn cargo_builds_queries_with_an_explicit_runtime_dependency() {
    let verifier = PathBuf::from(std::env::var_os("VERUS_QUERY_TEST_VERIFIER").unwrap());
    let artifacts = verifier.parent().unwrap();
    let project = tempfile::tempdir().unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..").canonicalize().unwrap();
    std::fs::create_dir(project.path().join("src")).unwrap();
    // Use TOML literal strings for repository paths, including spaces.
    std::fs::write(
        project.path().join("Cargo.toml"),
        format!(
            r#"
[package]
name = "query_client"
version = "0.1.0"
edition = "2021"
[dependencies]
vstd = {{ path = '{root}/source/vstd' }}
verus_meter_runtime = {{ path = '{root}/source/verus-meter/runtime' }}
[package.metadata.verus]
verify = true
"#,
            root = root.display()
        ),
    )
    .unwrap();
    std::fs::copy(root.join("rust-toolchain.toml"), project.path().join("rust-toolchain.toml"))
        .unwrap();
    let code = r#"use vstd::prelude::*;
verus! {
    #[queryable_peak_memory]
    fn foo(n: u16) -> u16 resources peak(memory) <= 1024 + n { n }
}
fn main() {
    assert_eq!(foo(10), 10);
    assert_eq!(foo::peak_memory_bound(10).unwrap().to_u64().unwrap(), 1034);
}
"#;
    std::fs::write(project.path().join("src/main.rs"), code).unwrap();
    let mut paths = vec![artifacts.to_path_buf()];
    paths.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap()));
    let build = || {
        Command::new(artifacts.join(format!("cargo-verus{}", std::env::consts::EXE_SUFFIX)))
            .current_dir(project.path())
            .args(["verus", "build", "--release", "--offline"])
            .env("PATH", std::env::join_paths(&paths).unwrap())
            .env("CARGO_TARGET_DIR", project.path().join("target"))
            .output()
            .unwrap()
    };
    succeeds(&build());
    let executable =
        project.path().join(format!("target/release/query_client{}", std::env::consts::EXE_SUFFIX));
    succeeds(&Command::new(&executable).output().unwrap());
    std::fs::write(
        project.path().join("src/main.rs"),
        code.replace("1024 + n", "2048 + n").replace("1034", "2058"),
    )
    .unwrap();
    succeeds(&build());
    succeeds(&Command::new(executable).output().unwrap());
}
