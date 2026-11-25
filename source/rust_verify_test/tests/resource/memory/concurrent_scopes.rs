//! Cross-thread observations use the workers covered by the nearest budgeted scope.
use super::support::{rejects, verifies};

const SPAWN: &str = "let h = std::thread::spawn(move || {
    let scratch = Vec::<u8>::with_capacity(256); drop(scratch);
});";
const JOIN: &str = "let done = h.join().unwrap();";

fn run(body: &str) -> String {
    format!("fn run() resources peak(memory) <= 1024 {{ {body} }}")
}

#[test]
fn current_and_peak_diverge_after_join() {
    let body = format!(
        "{SPAWN} assert(current(memory) <= LIVE); {JOIN}
        assert(current(memory) <= 0); assert(peak(memory) <= HIGH);"
    );
    let code = run(&body);
    verifies("scope_exact", &code.replace("LIVE", "289").replace("HIGH", "289"));
    rejects(
        "scope_current_short",
        &code.replace("LIVE", "288").replace("HIGH", "289"),
        "live 289 bytes exceeds bound 288",
    );
    rejects(
        "scope_history_short",
        &code.replace("LIVE", "289").replace("HIGH", "288"),
        "peak 289 bytes exceeds bound 288",
    );
}

#[test]
fn current_failure_labels_the_worker_with_outstanding_storage() {
    let code = r#"use vstd::prelude::*;
        verus! {
        fn run() resources peak(memory) <= 1024 {
            let first = std::thread::spawn(move || {});
            let second = std::thread::spawn(move || {
                let scratch = Vec::<u8>::with_capacity(256); drop(scratch);
            });
            BEFORE_JOIN
            let done = first.join().unwrap();
            AFTER_JOIN
            let done = second.join().unwrap();
        }
        }"#;
    let checkpoint = "assert(current(memory) <= 200);";
    // The first worker has no scratch at either checkpoint. The publisher accounts separately
    // for its handle and completion tag until the first join.
    for (name, before, after) in
        [("both_outstanding", checkpoint, ""), ("first_joined", "", checkpoint)]
    {
        let source = code.replace("BEFORE_JOIN", before).replace("AFTER_JOIN", after);
        let error = crate::verify_one_file(name, source, &[]).unwrap_err();
        let [diagnostic] = error.errors.as_slice() else { panic!("{:?}", error.errors) };
        assert!(
            diagnostic.message.contains("current(memory) assertion failed"),
            "{}",
            diagnostic.rendered
        );
        let labels: Vec<_> = diagnostic
            .spans
            .iter()
            .filter(|span| {
                span.label.as_deref().is_some_and(|label| label.starts_with("publication "))
            })
            .collect();
        assert!(
            matches!(labels.as_slice(), [span] if span.text[0].text.contains("let second =")),
            "{}",
            diagnostic.rendered
        );
    }
}

#[test]
fn sections_bill_their_descendants_and_compose_with_the_parent() {
    let code = run(&format!(
        "resources peak(memory) <= LIMIT {{ {SPAWN}
        resources peak(memory) <= 0 {{ assert(current(memory) <= 0); }} {JOIN} }}"
    ));
    verifies("scope_relative", &code.replace("LIMIT", "289"));
    rejects("scope_section_short", &code.replace("LIMIT", "288"), "section memory budget exceeded");
    let parent = run(&format!(
        "let saved = Box::new([0u8; 512]);
        resources peak(memory) <= 600 {{ {SPAWN} {JOIN} }} drop(saved);"
    ));
    rejects("scope_live_parent", &parent, "peak 1120 bytes exceeds budget 1024");
    for (name, exit) in [("early", "return;"), ("normal", "drop(h);")] {
        rejects(
            name,
            &run(&format!("resources peak(memory) <= 512 {{ {SPAWN} {exit} }}")),
            "outstanding descendant at memory section exit",
        );
    }
}

#[test]
fn worker_sections_have_their_own_history() {
    let nested = run(&format!(
        "let outer = std::thread::spawn(move || {{
        resources peak(memory) <= 512 {{ {SPAWN} {JOIN} assert(peak(memory) <= LIMIT); }}
    }}); let done = outer.join().unwrap();"
    ));
    verifies("worker_local_scope", &nested.replace("LIMIT", "289"));
    rejects(
        "worker_descendant_peak",
        &nested.replace("LIMIT", "288"),
        "peak 289 bytes exceeds bound 288",
    );
    let ancestor = run(&format!(
        "let h = std::thread::spawn(move || {{
        assert(peak(memory) <= 1024);
    }}); {JOIN}"
    ));
    rejects(
        "ancestor_history",
        &ancestor,
        "cross-thread reference to an ancestor's memory checkpoint",
    );
}

#[test]
fn peak_history_follows_branches_and_loop_back_edges() {
    verifies(
        "scope_alternative",
        &format!(
            "fn run(large: bool) resources peak(memory) <= 1024 {{
        if large {{ {SPAWN} {JOIN} }} else {{ assert(peak(memory) <= 1); }} }}"
        ),
    );
    let code = format!(
        "fn run(n:u16) resources peak(memory) <= 1024 {{ let mut i=0u16;
        while i<n invariant i<=n, decreases n-i, {{
            assert(peak(memory) <= HIGH); {SPAWN} {JOIN} i+=1; }} }}"
    );
    verifies("scope_previous_visit", &code.replace("HIGH", "512"));
    rejects("scope_loop_short", &code.replace("HIGH", "100"), "peak 293 bytes exceeds bound 100");
}

#[test]
fn counted_section_uses_the_live_family_and_proves_it_closed() {
    let body = r#"fn run(n:u16) requires n<=4, resources peak(memory)<=8192 {
        resources peak(memory)<=4096 {
            let mut handles=Vec::with_capacity(n as usize); let mut i=0u16;
            while i<n invariant n<=4,i<=n,handles.len()==i,decreases n-i, {
                let h=std::thread::spawn(move || {
                    let a=Vec::<u8>::with_capacity(256); drop(a);
                }); handles.push(h); i+=1;
            }
            assert(current(memory)<=LIMIT);
            while handles.len()>0 invariant n<=4,handles.len()<=n,decreases handles.len(), {
                let h=handles.pop().unwrap(); let r=h.join();
            }
            drop(handles); assert(current(memory)<=32);
        }
    }"#;
    verifies("counted_scope", &body.replace("LIMIT", "2048"));
    rejects("counted_scope_short", &body.replace("LIMIT", "128"), "current(memory) checkpoint");
    let program = body.replace("LIMIT", "2048");
    let early =
        |before: &str| program.replace(before, &format!("if n == 1 {{ return; }} {before}"));
    verifies("counted_exit_after_drain", &early("drop(handles);"));
    rejects(
        "counted_exit_before_drain",
        &early("while handles.len()>0"),
        "an outstanding descendant at memory section exit",
    );
}

#[test]
fn worker_current_combines_imported_backing_with_its_child() {
    let code = r#"fn run() resources peak(memory) <= 2048 {
        let backing = std::sync::Arc::new(0u64);
        let peer = backing.clone();
        let outer = std::thread::spawn(move || {
            let child = std::thread::spawn(move || {
                let scratch = Vec::<u8>::with_capacity(256); drop(scratch);
            });
            assert(current(memory) <= LIMIT);
            let done = child.join().unwrap(); drop(peer);
        });
        let done = outer.join().unwrap(); drop(backing);
    }"#;
    verifies("combined_subtree", &code.replace("LIMIT", "321"));
    rejects("omitted_backing", &code.replace("LIMIT", "320"), "321 bytes exceeds budget 320");
    // An explicit section starts after the worker received the backing.
    let relative = code
        .replace(
            "let child =",
            "resources peak(memory) <= 320 { assert(current(memory) <= 0); let child =",
        )
        .replace("drop(peer);", "} drop(peer);");
    verifies("entry_backing_belongs_to_parent", &relative.replace("LIMIT", "289"));
    rejects(
        "section_still_owes_child",
        &relative.replace("LIMIT", "288"),
        "live 289 bytes exceeds bound 288",
    );
}

#[test]
fn a_checkpoint_uses_the_actual_held_mutex() {
    let code = r#"fn run() resources peak(memory) <= 1024 {
        let lock = std::sync::Arc::new(std::sync::Mutex::new(0u8));
        let peer = PEER;
        let h = std::thread::spawn(move || {
            let guard = peer.lock();
            let scratch = Vec::<u8>::with_capacity(256); drop(scratch); drop(guard);
        });
        let guard = lock.lock(); let local = Vec::<u8>::with_capacity(256);
        assert(current(memory) <= 400); drop(local); drop(guard);
        let done = h.join().unwrap();
    }"#;
    verifies("scope_same_guard", &code.replace("PEER", "lock.clone()"));
    rejects(
        "scope_distinct_guards",
        &code.replace("PEER", "std::sync::Arc::new(std::sync::Mutex::new(0u8))"),
        "current(memory) checkpoint",
    );
}

#[test]
fn a_worker_rebinds_a_descendants_symbolic_bytes_at_its_checkpoint() {
    let code = r#"fn run(n: u16) requires n <= 128, resources peak(memory) <= 8192 {
        let parent = std::thread::spawn(move || {
            requires(n <= 128);
            resources peak(memory) <= 2048 {
                let child = std::thread::spawn(move || {
                    let a = Vec::<u8>::with_capacity(n as usize); drop(a);
                });
                assert(current(memory) <= LIMIT);
                let done = child.join().unwrap();
            }
        });
        let done = parent.join().unwrap();
    }"#;
    verifies("local_capture", &code.replace("LIMIT", "512"));
    rejects("local_capture_short", &code.replace("LIMIT", "64"), "current(memory) checkpoint");
}

#[test]
fn a_section_covering_publications_requires_a_fixed_bound() {
    let body = format!(
        "fn work(n:u16) resources peak(memory) <= n + 512 {{
        resources peak(memory) <= n + 320 {{ {SPAWN} {JOIN} }} }}"
    );
    rejects(
        "symbolic_spawn_section",
        &body,
        "entry-dependent section bound covering worker publications",
    );
}
