//! The last strong reference can be in the publisher or inside a worker's wrapper.
use super::*;

fn nested(collection: &str, after_push: &str) -> String {
    let publish =
        format!("let keep = root.clone(); let root = std::sync::Arc::new(root); {PUBLISH}");
    program(0, &publish, collection)
        .replace("41 + b", "65 + b")
        .replace("handles.push(job);", &format!("handles.push(job); {after_push}"))
}

fn verify_bounds(name: &str, source: String, bounds: &[u64]) {
    assert_vir_error_msg(crate::verify_one_file(name, source.clone(), &[]).unwrap_err(), GLOBAL);
    for &bytes in bounds {
        let short = source.replace(&format!("<= {bytes});"), &format!("<= {});", bytes - 1));
        assert_ne!(source, short);
        assert_vir_error_msgs(
            crate::verify_one_file(&format!("{name}_below_{bytes}"), short, &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn the_publisher_can_release_its_clone_after_storing_the_worker() {
    let collect = COLLECT.replace("<= 166", "<= 214").replace("<= 73", "<= 97");
    let source = nested(
        &collect,
        r#"
        if n == 2 && i == 1 && b == 19 { assert(current(memory) <= 222); }
        drop(keep);
    "#,
    );
    // Two distinct 59-byte backings. The last publisher handle adds 8 bytes
    // until its drop. After a partial drain the last wrapper still owns 59.
    verify_bounds("publisher_first", source, &[222, 214, 97]);
}

#[test]
fn dropping_the_joined_wrapper_keeps_the_publishers_clone_live() {
    let source = nested(
        "drop(handles); assert(current(memory) <= 6);",
        r#"
        if n == 2 && b == 19 { assert(current(memory) <= 138); }
        let wrapper = handles.pop().unwrap().join().unwrap();
        drop(wrapper);
        if n == 2 && b == 19 { assert(current(memory) <= 113); }
        drop(keep);
        if n == 2 { assert(current(memory) <= 46); }
    "#,
    )
    .replace("handles.len() == i", "handles.len() == 0");
    let consumed = source
        .replace("move || root", "move || drop(root)")
        .replace("let wrapper = ", "")
        .replace("drop(wrapper);", "");
    verify_bounds("worker_first", source, &[113]);
    verify_bounds("worker_consumes_wrapper", consumed, &[113]);
}

fn crossed_visits(requirement: &str, drain: &str) -> String {
    r#"
    use vstd::prelude::*;
    verus! {
        fn mixed(n: u16) requires REQUIREMENT, resources peak(memory) <= 130 * n + 256 {
            let mut left = Vec::with_capacity(n as usize);
            let mut right = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, left.len() == i, right.len() == i, decreases n - i, {
                let inner = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
                let keep = inner.clone();
                let a = std::sync::Arc::new(inner.clone());
                let b = std::sync::Arc::new(inner);
                left.push(std::thread::spawn(move || a));
                right.push(std::thread::spawn(move || b));
                drop(keep);
                i += 1;
            }
            if n == 2 { assert(current(memory) <= 302); }
            DRAIN
            let newer = right.pop().unwrap().join().unwrap();
            let older = right.pop().unwrap().join().unwrap(); drop(older);
            let other = left.pop().unwrap().join().unwrap(); drop(other);
            // The older left slot and the newer right result each keep one
            // 59-byte buffer. The two drops could not retire either visit.
            if n == 2 { assert(current(memory) <= 259); }
            drop(newer);
            if n == 2 { assert(current(memory) <= 168); }
            let last = left.pop().unwrap().join().unwrap(); drop(last);
            drop(left); drop(right);
            assert(current(memory) <= 4);
        }
    }
    "#
    .replace("REQUIREMENT", requirement)
    .replace("DRAIN", drain)
}

#[test]
fn dropping_wrappers_from_different_visits_keeps_both_inner_buffers() {
    let source = crossed_visits(
        "2 <= n",
        r#"
            while left.len() > 2 invariant left.len() == right.len(), 2 <= left.len() <= n,
                decreases left.len(),
            {
                let a = left.pop().unwrap().join().unwrap();
                let b = right.pop().unwrap().join().unwrap();
                drop(a); drop(b);
            }
    "#,
    );
    verify_bounds("crossed_visits", source, &[259, 168]);
}

#[test]
fn explicit_pops_must_consume_every_published_worker() {
    let source = crossed_visits("n == 2", "");
    verify_bounds("explicit_final_joins", source.clone(), &[]);
    let lost = source.replace("let last = left.pop().unwrap().join().unwrap(); drop(last);", "");
    let mut errors = crate::verify_one_file("missing_final_join", lost, &[]).unwrap_err();
    errors.errors.sort_by(|left, right| left.message.cmp(&right.message));
    assert_vir_error_msgs(
        errors,
        &[
            "cannot discard outstanding worker handles",
            "conditional memory budget exceeded",
            GLOBAL,
        ],
    );
}
