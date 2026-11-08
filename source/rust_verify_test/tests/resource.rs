#![feature(rustc_private)]
#[macro_use]
mod common;

#[path = "resource/memory/mod.rs"]
mod memory;

// Suites formerly had separate binaries and temporary-file namespaces. Keep
// each test's inputs isolated now that the suites share one binary.
#[expect(
    clippy::result_large_err,
    reason = "Preserve the upstream harness error type for its existing diagnostic assertions"
)]
fn verify_one_file(
    name: &str,
    code: String,
    options: &[&str],
) -> Result<common::TestErr, common::TestErr> {
    let thread = std::thread::current();
    let test = thread.name().expect("resource tests run on named test threads");
    let namespace = test.replace("::", "-");
    common::verify_one_file(&format!("{namespace}-{name}"), code, options)
}
