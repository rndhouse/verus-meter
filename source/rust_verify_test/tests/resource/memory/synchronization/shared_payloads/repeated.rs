//! Reacquiring a shared mutex and acquiring an independently returned mutex
//! exercise different identities even when only one lock statement is present.
use super::{CHECKPOINT, LINKED, diagnostics};

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

fn shared_loop(write: &str, observe: &str) -> String {
    format!(
        r#"
        fn work(n: u8, b: u8, write: bool) resources peak(memory) <= 16384 {{
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::with_capacity(3)));
            let peer = cell.clone();
            let writer = std::thread::spawn(move || {{
                let mut i = 0u8;
                while i < n invariant i <= n, decreases n - i, {{
                    if !write {{ i += 1; continue; }}
                    let r = peer.lock();
                    if r.is_err() {{ return; }}
                    {{
                        let mut g = r.unwrap();
                        {write}
                    }}
                    i += 1;
                }}
            }});
            let reader = std::thread::spawn(move || {{
                let r = cell.lock();
                if r.is_err() {{ return; }}
                let mut g = r.unwrap();
                let item = g.pop();
                {observe}
            }});
            let second = reader.join();
            let first = writer.join();
        }}
    "#
    )
}

const READER_BOUNDS: &str = "if n == 0 || !write { assert(current(memory) <= 73); }
                              else if b == 37 { assert(current(memory) <= 107); }";

#[test]
fn repeated_alias_writes_include_zero_iterations_and_skipped_writes() {
    // 70 local bytes plus either the original three reserved bytes or a
    // replacement reservation. Collect the reader first in all cases.
    let program = shared_loop("*g = Vec::with_capacity(b as usize);", READER_BOUNDS);
    diagnostics("repeated_replace", &program, &[LINKED]);
    diagnostics(
        "repeated_initial_short",
        &program.replace("<= 73", "<= 72"),
        &[LINKED, CHECKPOINT],
    );
    diagnostics(
        "repeated_write_short",
        &program.replace("<= 107", "<= 106"),
        &[LINKED, CHECKPOINT],
    );
}

#[test]
fn helpers_acquire_replace_and_release_across_loop_visits() {
    let helpers = r#"
        type G<'a> = std::sync::MutexGuard<'a, Vec<u8>>;
        fn acquire(m: &std::sync::Mutex<Vec<u8>>) -> std::sync::LockResult<G<'_>>
            resources peak(memory) <= 256 { m.lock() }
        fn replace(mut g: G<'_>, b: u8) resources peak(memory) <= 1024 {
            *g = Vec::with_capacity(b as usize);
        }
    "#;
    let workers = shared_loop("replace(g, b);", READER_BOUNDS)
        .replace("peer.lock()", "acquire(&*peer)")
        .replace("cell.lock()", "acquire(&*cell)");
    let program = format!("{helpers} {workers}");
    let helper = "mutex intervals awaiting global";
    diagnostics("factored_repeated_replace", &program, &[LINKED, helper]);
    diagnostics(
        "factored_repeated_short",
        &program.replace("<= 107", "<= 106"),
        &[LINKED, helper, CHECKPOINT],
    );
}

#[test]
fn an_early_exit_before_the_loop_keeps_the_initial_reservation() {
    let program = shared_loop("*g = Vec::with_capacity(b as usize);", READER_BOUNDS)
        .replace("let mut i = 0u8;", "if !write { return; } let mut i = 0u8;")
        .replace("if !write { i += 1; continue; }", "");
    diagnostics("skipped_writer_loop", &program, &[LINKED]);
}

#[test]
fn one_visit_cannot_bound_a_growing_shared_payload() {
    // A finite candidate obtained from one push is not closed under the next push.
    diagnostics(
        "repeated_append",
        &shared_loop("g.push(b);", ""),
        &[LINKED, "a repeated mutex release falls outside its proposed contents"],
    );
}

fn distinct_mutexes(precondition: &str, collect: &str) -> String {
    format!(
        r#"
        fn work(n: u8) {precondition} resources peak(memory) <= 65536 {{
            let mut jobs = Vec::with_capacity(n as usize);
            let mut i = 0u8;
            while i < n invariant i <= n, jobs.len() == i, decreases n - i, {{
                let job = std::thread::spawn(move || {{
                    let mut items = Vec::new();
                    let inner = Vec::<u8>::with_capacity(i as usize);
                    items.push(inner);
                    std::sync::Mutex::new(items)
                }});
                jobs.push(job);
                i += 1;
            }}
            {collect}
        }}
    "#
    )
}

#[test]
fn neighbouring_join_records_keep_their_own_reservations_after_unlock() {
    let check = |selected: &str, discarded: &str, limit: usize| {
        let collect = format!(
            r#"
            while jobs.len() > 2 invariant 2 <= jobs.len() <= n, decreases jobs.len(), {{
                let other = jobs.pop().unwrap().join().unwrap();
                drop(other);
            }}
            let high = jobs.pop().unwrap().join().unwrap();
            let low = jobs.pop().unwrap().join().unwrap();
            drop(jobs);
            drop({discarded});
            let r = {selected}.lock();
            if r.is_err() {{ return; }}
            let mut g = r.unwrap();
            let item = g.pop();
            drop(g);
            drop({selected});
            assert(current(memory) <= {limit});
            drop(item);
        "#
        );
        distinct_mutexes("requires n >= 2,", &collect)
    };
    // Two u8 locals and Option<Vec<u8>> cost 27 bytes. Only the worker at
    // index one contributes a further byte owned by the popped vector.
    diagnostics("selected_first", &check("low", "high", 27), &[GLOBAL]);
    diagnostics("selected_second", &check("high", "low", 28), &[GLOBAL]);
    diagnostics(
        "selected_neighbour_short",
        &check("high", "low", 27),
        &[GLOBAL, "conditional memory budget exceeded"],
    );
    // A returned guard still selects the same joined worker's mutex.
    let helper = r#"fn pass<'a>(g: std::sync::MutexGuard<'a, Vec<Vec<u8>>>)
        -> std::sync::MutexGuard<'a, Vec<Vec<u8>>> resources peak(memory) <= 32 { g }"#;
    let checked = check("high", "low", 28)
        .replace("let mut g = r.unwrap();", "let held = r.unwrap(); let mut g = pass(held);");
    let program = format!("{helper} {checked}");
    let gate = "mutex intervals awaiting global";
    diagnostics("selected_returned_guard", &program, &[GLOBAL, gate]);
    diagnostics(
        "selected_returned_guard_short",
        &program.replace("<= 28", "<= 27"),
        &[GLOBAL, gate, "conditional memory budget exceeded"],
    );
}

#[test]
fn the_same_join_and_lock_statements_select_a_fresh_owner_each_iteration() {
    let collect = r#"
        while jobs.len() > 0 invariant jobs.len() <= n, decreases jobs.len(), {
            let cell = jobs.pop().unwrap().join().unwrap();
            let r = cell.lock();
            if r.is_err() { drop(r); } else {
                let mut g = r.unwrap();
                let item = g.pop();
                drop(g);
                drop(item);
            }
        }
    "#;
    diagnostics("drain_distinct_mutexes", &distinct_mutexes("", collect), &[GLOBAL]);
    let delegated = format!(
        r#"
        let drain = std::thread::spawn(move || {{
            let mut jobs = jobs;
            {collect}
        }});
        let done = drain.join();
    "#
    );
    diagnostics("worker_drains_distinct_mutexes", &distinct_mutexes("", &delegated), &[GLOBAL]);
}

#[test]
fn a_joined_box_can_come_from_any_successful_repeated_write() {
    let program = r#"
        fn work(n: u8) resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
            let peer = cell.clone();
            let keep = cell.clone();
            let writer = std::thread::spawn(move || {
                let mut i = 0u8;
                while i < n invariant i <= n, decreases n - i, {
                    let r = peer.lock();
                    if r.is_err() { return; }
                    let mut g = r.unwrap();
                    *g = Vec::new();
                    g.push(Box::new([7u8; 32]));
                    drop(g);
                    i += 1;
                }
            });
            let reader = std::thread::spawn(move || {
                let r = cell.lock();
                if r.is_err() { return None; }
                let mut g = r.unwrap();
                let item = g.pop();
                drop(g);
                item
            });
            let result = reader.join();
            let done = writer.join();
            drop(done);
            let item = result.unwrap();
            drop(keep);
            if n == 0 { assert(current(memory) <= 10); } else { assert(current(memory) <= 42); }
            drop(item);
        }
    "#;
    diagnostics("repeated_joined_box", program, &[LINKED]);
    diagnostics(
        "repeated_joined_box_short",
        &program.replace("<= 42", "<= 41"),
        &[LINKED, "conditional memory budget exceeded"],
    );
    // A nested lock helper contributes its frame and forwards the same guard.
    let acquire = r#"type M = std::sync::Mutex<Vec<Box<[u8; 32]>>>;
        type G<'a> = std::sync::MutexGuard<'a, Vec<Box<[u8; 32]>>>;
        fn lock(m: &M) -> std::sync::LockResult<G<'_>>
            resources peak(memory) <= 256 { m.lock() }
        fn acquire(m: &M) -> std::sync::LockResult<G<'_>>
            resources peak(memory) <= 512 { lock(m) }"#;
    let workers =
        program.replace("peer.lock()", "acquire(&*peer)").replace("cell.lock()", "acquire(&*cell)");
    let factored = format!("{acquire} {workers}");
    let helper = "mutex intervals awaiting global";
    diagnostics("helper_repeated_joined_box", &factored, &[LINKED, helper]);
    diagnostics(
        "helper_repeated_joined_box_short",
        &factored.replace("<= 42", "<= 41"),
        &[LINKED, helper, "conditional memory budget exceeded"],
    );
}

#[test]
fn a_shared_mutex_identity_cannot_supply_the_contents_to_a_mutating_helper() {
    let program = r#"
        fn append(m: &std::sync::Mutex<Vec<u8>>, b: u8) resources peak(memory) <= 1024 {
            let r = m.lock();
            if r.is_err() { return; }
            let mut g = r.unwrap();
            g.push(b);
        }
        fn work(b: u8) resources peak(memory) <= 16384 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
            let peer = cell.clone();
            let h = std::thread::spawn(move || { append(&*peer, b); });
            let result = h.join();
            drop(cell);
        }
    "#;
    diagnostics(
        "unbound_helper_write",
        program,
        &["without an acquisition-relative ownership interface"],
    );
}

#[test]
fn an_indexed_arc_without_a_protected_contents_relation_stays_opaque() {
    let program = r#"
        fn work(n: u8) resources peak(memory) <= 65536 {
            let mut jobs = Vec::with_capacity(n as usize);
            let mut i = 0u8;
            while i < n invariant i <= n, jobs.len() == i, decreases n - i, {
                let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::with_capacity(i as usize)));
                let job = std::thread::spawn(move || cell);
                jobs.push(job);
                i += 1;
            }
            while jobs.len() > 0 invariant jobs.len() <= n, decreases jobs.len(), {
                let cell = jobs.pop().unwrap().join().unwrap();
                let r = cell.lock();
                drop(r);
            }
        }
    "#;
    diagnostics("opaque_selected_arc_mutex", program, &["a lock without a checked mutex instance"]);
}
