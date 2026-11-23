//! Ownership published by a helper that acquires and releases a shared mutex.
use super::{CHECKPOINT, LINKED, diagnostics};

const HELPER: &str = "mutex intervals awaiting global";

#[test]
fn a_nested_helper_appends_to_whichever_contents_it_acquires() {
    let source = r#"
        type M = std::sync::Mutex<Vec<Box<[u8; 32]>>>;
        fn append(m: &M) resources peak(memory) <= 1024 {
            let r = m.lock();
            if r.is_err() { return; }
            let mut g = r.unwrap();
            g.push(Box::new([7u8; 32]));
        }
        fn nested(m: &M) resources peak(memory) <= 2048 { append(m); }
        fn work() resources peak(memory) <= 16384 {
            let cell = std::sync::Arc::new(M::new(Vec::new()));
            let peer = cell.clone();
            let extra = cell.clone();
            let writer = std::thread::spawn(move || { nested(&*peer); });
            let other = std::thread::spawn(move || {
                let r = extra.lock();
                if r.is_err() { return; }
                let mut g = r.unwrap();
                g.push(Box::new([2u8; 32]));
            });
            let reader = std::thread::spawn(move || {
                let r = cell.lock();
                if r.is_err() { return; }
                let mut g = r.unwrap();
                let item = g.pop();
                assert(current(memory) <= LIMIT);
            });
            let result = reader.join();
            let first = writer.join();
            let second = other.join();
        }
    "#;
    // Either writer may go first. Both boxes can survive until the pop,
    // one in the reader's Option and one in the remaining vector slot.
    let linked = "distinct mutexes = 1, linked acquisitions = 3";
    diagnostics("nested_internal_write", &source.replace("LIMIT", "146"), &[HELPER, linked]);
    diagnostics(
        "nested_internal_short",
        &source.replace("LIMIT", "145"),
        &[HELPER, linked, CHECKPOINT],
    );
}

#[test]
fn skipped_updates_preserve_the_initial_contents() {
    let source = r#"
        type M = std::sync::Mutex<Vec<Box<[u8; 32]>>>;
        fn append(m: &M, write: bool) resources peak(memory) <= 1024 {
            if !write { return; }
            let r = m.lock();
            if r.is_err() { return; }
            let mut g = r.unwrap();
            g.push(Box::new([7u8; 32]));
        }
        fn work(write: bool) resources peak(memory) <= 16384 {
            let cell = std::sync::Arc::new(M::new(Vec::new()));
            let peer = cell.clone();
            let writer = std::thread::spawn(move || { append(&*peer, write); });
            let reader = std::thread::spawn(move || {
                let r = cell.lock();
                if r.is_err() { return; }
                let mut g = r.unwrap();
                let item = g.pop();
                if write { assert(current(memory) <= LIMIT); }
                else { assert(current(memory) <= 75); }
            });
            let second = reader.join();
            let first = writer.join();
        }
    "#;
    diagnostics("internal_skipped", &source.replace("LIMIT", "107"), &[HELPER, LINKED]);
    diagnostics(
        "internal_skipped_short",
        &source.replace("LIMIT", "106"),
        &[HELPER, LINKED, CHECKPOINT],
    );
}

#[test]
fn an_internal_push_uses_an_independent_input_at_each_visit() {
    let source = r#"
        fn append(m: &std::sync::Mutex<Vec<u8>>, b: u8) resources peak(memory) <= 1024 {
            let r = m.lock();
            if r.is_err() { return; }
            let mut g = r.unwrap();
            g.push(b);
        }
        fn work(n: u8, b: u8) resources peak(memory) <= 16384 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
            let peer = cell.clone();
            let h = std::thread::spawn(move || {
                append(&*peer, b);
            });
            let result = h.join();
            drop(cell);
        }
    "#;
    let linked = "distinct mutexes = 1, linked acquisitions = 1";
    diagnostics("one_internal_push", source, &[HELPER, linked]);
    let repeated = source.replace(
        "append(&*peer, b);",
        r#"
        let mut i = 0u8;
        while i < n invariant i <= n, decreases n - i, {
            append(&*peer, b);
            i += 1;
        }"#,
    );
    diagnostics(
        "growing_internal_push",
        &repeated,
        &[HELPER, linked, "a repeated mutex release falls outside its proposed contents"],
    );
    let twice =
        source.replace("let r = m.lock();", "let first = m.lock(); drop(first); let r = m.lock();");
    diagnostics(
        "two_internal_sections",
        &twice,
        &["without an acquisition-relative ownership interface"],
    );
}

#[test]
fn an_allocation_kept_after_unlock_needs_its_own_lifetime() {
    let source = r#"
        type M = std::sync::Mutex<Vec<Box<[u8; 32]>>>;
        fn take(m: &M) resources peak(memory) <= 1024 {
            let r = m.lock();
            // Even granting success, the popped box can outlive this guard.
            assume(r.is_ok());
            let mut g = r.unwrap();
            let item = g.pop();
            drop(g);
            drop(item);
        }
        fn work() resources peak(memory) <= 16384 {
            let mut v = Vec::new();
            v.push(Box::new([7u8; 32]));
            let cell = std::sync::Arc::new(M::new(v));
            let peer = cell.clone();
            let h = std::thread::spawn(move || { take(&*peer); });
            let result = h.join();
            drop(cell);
        }
    "#;
    diagnostics(
        "detached_at_unlock",
        source,
        &["without an acquisition-relative ownership interface"],
    );
}
