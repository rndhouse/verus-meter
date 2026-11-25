//! Whole-operation bounds for executable populations. Each handle names one
//! occurrence until its join, including when stored and recovered in a loop.
use super::support::{exceeds, verifies};

const EXCLUSIVE: &str = "256 + 64 * n + (if n == 0 { 0 } else { b })";
const UNRESTRICTED: &str = "256 + 64 * n + n * b";
const FREE: &str = "drop(peer); let scratch = Vec::<u8>::with_capacity(b as usize); drop(scratch);";
const GUARDED: &str = "let guard = peer.lock();
    let scratch = Vec::<u8>::with_capacity(b as usize);
    drop(scratch); drop(guard);";

fn batch(worker: &str, allowance: &str) -> String {
    format!(
        r#"
        fn work(n: u16, b: u16)
            requires 0 <= n as int * b as int <= 4294967296int,
            resources peak(memory) <= {allowance}
        {{
            let lock = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {{
                let peer = lock.clone();
                let job = std::thread::spawn(move || {{ {worker} }});
                handles.push(job);
                i += 1;
            }}
            while handles.len() > 0 invariant handles.len() <= n, decreases handles.len(), {{
                let job = handles.pop().unwrap();
                let result = job.join();
            }}
        }}
    "#
    )
}

#[test]
fn symbolic_population_uses_only_compatible_worker_phases() {
    // This precondition exposes the ordinary mathematical product's range to
    // the SMT query. These concrete callers also check it at the call boundary.
    let clients = "fn sizes() { work(0, 65535); work(1, 4096); work(50000, 4096); }";
    verifies("exclusive_population", &(batch(GUARDED, EXCLUSIVE) + clients));
    verifies("independent_population", &(batch(FREE, UNRESTRICTED) + clients));
    let two = batch(FREE, EXCLUSIVE)
        .replace("requires ", "requires n == 2, b == 4096, ")
        .replace("invariant ", "invariant n == 2, b == 4096, ");
    exceeds("two_reachable_buffers", &two);
}

#[test]
fn exclusion_requires_a_shared_instance_and_the_whole_buffer_lifetime() {
    let early = GUARDED.replace("drop(scratch); drop(guard);", "drop(guard); drop(scratch);");
    exceeds("survives_release", &batch(&early, EXCLUSIVE));
    let private = batch(GUARDED, EXCLUSIVE)
        .replace("lock.clone()", "std::sync::Arc::new(std::sync::Mutex::new(0u8))");
    exceeds("fresh_mutex_per_visit", &private);
}

#[test]
fn caller_can_reuse_scratch_after_the_population_drains() {
    let caller = "let local = Vec::<u8>::with_capacity(b as usize); drop(local);";
    let source = batch(GUARDED, "256 + 64 * n + b");
    let (before, drain) = source.split_once("while handles.len() > 0").unwrap();
    exceeds("caller_and_live_workers", &format!("{before}{caller} while handles.len() > 0{drain}"));
    let (body, _) = source.rsplit_once('}').unwrap();
    verifies("caller_after_collection", &format!("{body}{caller} }}"));
}

#[test]
fn immediate_join_reuses_one_workers_storage() {
    verifies(
        "immediate_join",
        r#"
        fn work(n: u16, b: u16)
            resources peak(memory) <= 128 + (if n == 0 { 0 } else { b })
        {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let handle = std::thread::spawn(move || {
                    let scratch = Vec::<u8>::with_capacity(b as usize); drop(scratch);
                });
                let result = handle.join();
                i += 1;
            }
        }
    "#,
    );
}

#[test]
fn an_overflowing_source_population_budget_fails_its_range_check() {
    let code = batch(GUARDED, "256 + 18446744073709551615u64 * n + b");
    let err = crate::verify_one_file(
        "population_overflow",
        format!("use vstd::prelude::*; verus! {{ {code} }}"),
        &[],
    )
    .unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("memory budget arithmetic exceeds u64")));
}

#[test]
fn a_completed_worker_retains_its_scalar_until_collection() {
    // Each slot and tag occupy nine bytes. Returning a u64 adds eight bytes
    // per outstanding completion if all workers finish before the first join.
    verifies("unit_results", &batch("()", "256 + 9 * n"));
    verifies("scalar_results", &batch("42u64", "256 + 17 * n"));
    exceeds("missing_scalar_result_byte", &batch("42u64", "256 + 16 * n"));
}

#[test]
fn different_critical_sections_can_overlap_across_visits() {
    let second = GUARDED.replace("peer.lock()", "other.lock()");
    let source = batch(&format!("{GUARDED} {second}"), "256 + 64 * n + 2 * b")
        .replace(
            "let mut handles",
            "let lock2 = std::sync::Arc::new(std::sync::Mutex::new(1u8)); let mut handles",
        )
        .replace(
            "let job = std::thread::spawn",
            "let other = lock2.clone(); let job = std::thread::spawn",
        );
    verifies("two_mutex_classes", &source);
    exceeds("two_mutex_classes_overlap", &source.replace("2 * b", "b"));
}

#[test]
fn inclusive_loop_publishes_even_at_zero() {
    // n >= i includes visit zero. An allowance that treats n as the number
    // published would miss a real buffer on that visit.
    let source = batch(GUARDED, "256 + 64 * (n + 1) + b")
        .replace("requires ", "requires n < 65535, ")
        .replace("while i < n invariant i <= n", "while n >= i invariant n < 65535, i <= n + 1")
        .replace("decreases n - i", "decreases n + 1 - i")
        .replace("handles.len() <= n,", "handles.len() <= n + 1,")
        .replace("Vec::with_capacity(n as usize)", "Vec::with_capacity(n as usize + 1)");
    verifies("inclusive_workers", &source);
    exceeds(
        "inclusive_worker_at_zero",
        &source.replace("64 * (n + 1) + b", "64 * (n + 1) + (if n == 0 { 0 } else { b })"),
    );
}

#[test]
fn unlocking_before_freeing_the_returned_buffer_exceeds_the_batch_contract() {
    let example = include_str!(
        "../../../../../examples/resource/memory/concurrent/expected-failures/unlock_before_drop.rs"
    );
    let failure = crate::verify_one_file("unlock_before_drop", example.into(), &["--no-cheating"])
        .unwrap_err();
    assert!(!failure.errors.is_empty());
    assert!(
        failure.errors.iter().all(|error| error.message.contains("memory budget exceeded")
            && error.spans.iter().any(|span| span.text.iter().any(|line| {
                line.text.contains("resources peak(memory) <= run_workers_budget(")
            }))),
        "{:?}",
        failure.errors
    );
}
