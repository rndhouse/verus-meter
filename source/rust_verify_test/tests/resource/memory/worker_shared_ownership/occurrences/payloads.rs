//! Inner allocations travel with the particular outer allocation that owns them.
use super::*;

#[test]
fn privately_owned_inner_backings_follow_each_visit() {
    let source = program(0, &format!("let root = std::sync::Arc::new(root); {PUBLISH}"), COLLECT)
        .replace("41 + b", "65 + b")
        .replace("<= 166", "<= 214")
        .replace("<= 73", "<= 97");
    assert_vir_error_msg(
        crate::verify_one_file("nested", source.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    for (name, exact, short) in [("outstanding", "<= 214", "<= 213"), ("last", "<= 97", "<= 96")] {
        assert_vir_error_msgs(
            crate::verify_one_file(name, source.replace(exact, short), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn two_private_paths_keep_one_buffer_per_visit() {
    let publish = format!(
        r#"
        let left = std::sync::Arc::new(root.clone());
        let right = std::sync::Arc::new(root);
        let root = std::sync::Arc::new(Pair {{ a: left, b: right }});
        {PUBLISH}
    "#
    );
    let pair = "struct Pair { a: std::sync::Arc<std::sync::Arc<Vec<u8>>>, b: std::sync::Arc<std::sync::Arc<Vec<u8>>> }";
    let source = program(0, &publish, COLLECT)
        .replace("fn fresh", &format!("{pair}\nfn fresh"))
        .replace("41 + b", "121 + b")
        .replace("<= 166", "<= 326")
        .replace("<= 73", "<= 153");
    assert_vir_error_msg(
        crate::verify_one_file("private_paths", source.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    assert_vir_error_msgs(
        crate::verify_one_file("private_short", source.replace("<= 153", "<= 152"), &[])
            .unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}

/// Each outer allocation owns two real clones of the same fixed root.
const SHARED: &str = r#"
    use vstd::prelude::*;
    verus! {
    struct Pair { a: std::sync::Arc<Vec<u8>>, b: std::sync::Arc<Vec<u8>> }
    fn shared(n: u16) requires n > 0, resources peak(memory) <= 41 * n + 256 {
        let inner = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
        let mut jobs = Vec::with_capacity(n as usize);
        let mut i = 0u16;
        while i < n invariant i <= n, jobs.len() == i, decreases n - i, {
            let outer = std::sync::Arc::new(Pair { a: inner.clone(), b: inner.clone() });
            jobs.push(std::thread::spawn(move || outer));
            i += 1;
        }
        if n == 2 { assert(current(memory) <= 177); }
        while jobs.len() > 1 invariant 1 <= jobs.len() <= n, decreases jobs.len(), {
            let outer = jobs.pop().unwrap().join().unwrap(); drop(outer);
        }
        let last = jobs.pop().unwrap().join().unwrap(); drop(jobs);
        assert(current(memory) <= 111);
        drop(last);
        assert(current(memory) <= 71);
        drop(inner);
        assert(current(memory) <= 4);
    }
    }
"#;

#[test]
fn distinct_wrappers_share_one_inner_allocation() {
    assert_vir_error_msg(crate::verify_one_file("shared", SHARED.into(), &[]).unwrap_err(), GLOBAL);
    for (name, exact, short) in [("two_outer", "<= 177", "<= 176"), ("inner", "<= 71", "<= 70")] {
        assert_vir_error_msgs(
            crate::verify_one_file(name, SHARED.replace(exact, short), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn last_wrapper_keeps_its_inner_alive_without_a_publisher_alias() {
    let source = SHARED
        .replace("drop(inner);", "")
        .replace("while jobs.len()", "drop(inner); while jobs.len()")
        .replace("<= 111", "<= 103")
        .replace("assert(current(memory) <= 71);", "");
    assert_vir_error_msg(
        crate::verify_one_file("restored", source.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    assert_vir_error_msgs(
        crate::verify_one_file("restored_short", source.replace("<= 103", "<= 102"), &[])
            .unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}

#[test]
fn caller_pays_for_the_input_through_every_wrapper() {
    let caller = r#"
        fn caller() resources peak(memory) <= 438 {
            let input = Vec::<u8>::with_capacity(100);
            shared(2, input);
            assert(current(memory) <= 0);
            let next = Vec::<u8>::with_capacity(414); drop(next);
        }
    "#;
    let source = SHARED
        .replace("fn shared(n: u16)", "fn shared(n: u16, input: Vec<u8>)")
        .replace("Vec::<u8>::with_capacity(19)", "input")
        .replace("<= 177", "<= 158")
        .replace("<= 111", "<= 92")
        .replace("<= 71", "<= 52")
        .replace("struct Pair", &format!("{caller}\nstruct Pair"));
    assert_vir_error_msg(
        crate::verify_one_file("caller", source.clone(), &[]).unwrap_err(),
        GLOBAL,
    );
    // 100 bytes of input coexist with the callee's declared 338-byte allowance.
    let short = source.replace("<= 438", "<= 437").replace("capacity(414)", "capacity(100)");
    assert_vir_error_msgs(
        crate::verify_one_file("call_short", short, &[]).unwrap_err(),
        &["conditional memory budget exceeded", GLOBAL],
    );
}

/// Visit i embeds a distinct job whose returned buffer reserves i + 7 bytes.
/// At n = 2 the first pop delivers 8 bytes while the other job is outstanding.
/// The second pop delivers 7 bytes and both completion tags have been released.
const JOBS: &str = r#"
use vstd::prelude::*;
verus! {
    fn run(n: u16) requires 1 <= n <= 3, resources peak(memory) <= 512 {
        let mut jobs = Vec::with_capacity(n as usize);
        let mut i = 0u16;
        while i < n invariant n <= 3, i <= n, jobs.len() == i, decreases n - i, {
            let inner = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize + 7));
            let outer = std::sync::Arc::new(inner);
            jobs.push(std::thread::spawn(move || outer));
            i += 1;
        }
        while jobs.len() > 0 invariant n <= 3, jobs.len() <= n, decreases jobs.len(), {
            let outer = jobs.pop().unwrap().join().unwrap();
            let slot = std::sync::Arc::into_inner(outer);
            match slot {
                Some(job) => {
                    let buf = job.join().unwrap();
                    if n == 2 && jobs.len() == 1 { assert(current(memory) <= 102); }
                    if n == 2 && jobs.len() == 0 { assert(current(memory) <= 75); }
                    drop(buf);
                },
                None => {},
            }
        }
        drop(jobs);
        assert(current(memory) <= 4);
    }
}
"#;

#[test]
fn each_embedded_job_keeps_its_own_publication() {
    assert_vir_error_msg(crate::verify_one_file("jobs", JOBS.into(), &[]).unwrap_err(), GLOBAL);
    for (name, exact, short) in [("later", "<= 102", "<= 101"), ("earlier", "<= 75", "<= 74")] {
        assert_vir_error_msgs(
            crate::verify_one_file(name, JOBS.replace(exact, short), &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn a_transported_job_still_requires_a_unique_extraction_and_join() {
    let keep = JOBS
        .replace("let slot =", "let keep = outer.clone(); let slot =")
        .replace("None => {},\n            }", "None => {},\n            } drop(keep);");
    assert_vir_error_msg(
        crate::verify_one_file("aliased_job", keep, &[]).unwrap_err(),
        "extracting a shared payload without exclusive ownership",
    );
    let lost = JOBS
        .replace(
            "jobs.len() > 0 invariant n <= 3, jobs.len() <= n",
            "jobs.len() > 1 invariant n <= 3, 1 <= jobs.len() <= n",
        )
        .replace(
            "drop(jobs);",
            "let last = jobs.pop().unwrap().join().unwrap(); drop(jobs); drop(last);",
        );
    assert_vir_error_msg(
        crate::verify_one_file("lost_job", lost, &[]).unwrap_err(),
        "detached workers in a memory accounting scope",
    );
}

#[test]
fn each_visit_can_take_a_different_caller_owned_buffer() {
    // The caller pays 48 bytes for the two Vec headers and 7 + 19 for their
    // buffers throughout the 512-byte call. All 74 bytes are reusable on return.
    let source = r#"
use vstd::prelude::*;
verus! {
    fn consume(mut input: Vec<Vec<u8>>, n: u16)
        requires input.len() == n, n <= 3,
        resources peak(memory) <= 512
    {
        let mut jobs = Vec::with_capacity(3);
        let mut i = 0u16;
        while i < n invariant n <= 3, i <= n, jobs.len() == i, input.len() == n - i,
            decreases n - i,
        {
            let buf = input.pop().unwrap();
            let inner = std::sync::Arc::new(buf);
            let outer = std::sync::Arc::new(inner);
            jobs.push(std::thread::spawn(move || outer));
            i += 1;
        }
        if n == 2 { assert(current(memory) <= 206); }
        drop(input);
        while jobs.len() > 0 invariant n <= 3, jobs.len() <= n, decreases jobs.len(), {
            let outer = jobs.pop().unwrap().join().unwrap(); drop(outer);
        }
        drop(jobs); assert(current(memory) <= 4);
    }
    fn caller() resources peak(memory) <= 586 {
        let mut input = Vec::with_capacity(2);
        let a = Vec::<u8>::with_capacity(7); input.push(a);
        let b = Vec::<u8>::with_capacity(19); input.push(b);
        consume(input, 2);
        assert(current(memory) <= 0);
        let reuse = Vec::<u8>::with_capacity(562); drop(reuse);
    }
}
    "#;
    assert_vir_error_msg(
        crate::verify_one_file("incoming", source.into(), &[]).unwrap_err(),
        GLOBAL,
    );
    for (name, short) in [
        ("local_short", source.replace("<= 206", "<= 205")),
        (
            "caller_short",
            source.replace("<= 586", "<= 585").replace("capacity(562)", "capacity(7)"),
        ),
    ] {
        assert_vir_error_msgs(
            crate::verify_one_file(name, short, &[]).unwrap_err(),
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}
