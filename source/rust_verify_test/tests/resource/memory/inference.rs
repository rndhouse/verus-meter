use crate::common::*;
use crate::verify_one_file;

#[test]
fn required_summary_identifies_the_loop_and_optional_summary_can_be_absent() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
        fn build() RETURN_TYPE resources peak(memory) <= 100000 {
            let mut buffers = Vec::<Box<u32>>::with_capacity(2);
            let mut i = 0usize;
            while i < 2
                invariant i <= 2, buffers.len() <= i,
                decreases 2-i,
            {
                if i * i < 2 {
                    let buffer = Box::new(7u32);
                    buffers.push(buffer);
                }
                i += 1;
            }
            RESULT
        }
        }
    "#;
    let error = verify_one_file(
        "required_summary_loop_origin",
        source.replace("RETURN_TYPE", "-> Vec<Box<u32>>").replace("RESULT", "buffers"),
        &[],
    )
    .unwrap_err();
    assert_eq!(error.errors.len(), 1);
    let diagnostic = &error.errors[0];
    assert!(diagnostic.message.contains("no precise helper summary can be inferred"));
    assert!(diagnostic.message.contains("loop ownership composition"));
    assert!(diagnostic.spans.iter().any(|span| span.is_primary
        && span.text.first().is_some_and(|line| line.text.contains("while i < 2"))));
    assert!(diagnostic.spans.iter().any(|span| !span.is_primary
        && span.label.as_deref() == Some("ownership summary required for this function")));

    // The same unsupported export must not reject a body that needs no summary.
    verify_one_file(
        "optional_summary_absent",
        source.replace("RETURN_TYPE", "").replace("RESULT", "drop(buffers);"),
        &[],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] owned_vector_capacity_is_inferred verus_code! {
        use vstd::prelude::*;
        fn append(mut v: Vec<u32>, cap: usize) -> (result: Vec<u32>)
            requires v.len() < cap,
            ensures result@ == v@.push(3),
            resources peak(memory) <= 32,
        { v.push(3); v }
        fn run() resources peak(memory) <= 64 {
            let v = Vec::<u32>::with_capacity(2);
            let mut v = append(v, 1);
            v.push(4);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consecutive_pushes_infer_all_required_slots verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            ensures final(v).len() == 2,
            resources peak(memory) <= 8,
        { v.push(1); v.push(2); }
        fn run() resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::with_capacity(2);
            append(&mut v);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consecutive_pushes_reject_insufficient_reservation verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            resources peak(memory) <= 8,
        { v.push(1); v.push(2); }
        fn run() resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::with_capacity(1);
            append(&mut v);
        }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] branches_keep_conditional_requirements verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, yes: bool)
            requires old(v).len() == 0,
            resources peak(memory) <= 9,
        { if yes { v.push(1); } }
        fn forward(v: &mut Vec<u32>, yes: bool)
            requires old(v).len() == 0,
            resources peak(memory) <= 18,
        { append(v, yes); }
        fn run() resources peak(memory) <= 42 {
            let mut v = Vec::<u32>::new();
            forward(&mut v, false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] guarded_push_needs_no_length_precondition verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, limit: usize)
            resources peak(memory) <= 16,
        { if v.len() < limit { v.push(1); } }
        fn run() resources peak(memory) <= 48 {
            let mut v = Vec::<u32>::with_capacity(2);
            append(&mut v, 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fill_through_nested_helper_infers_loop_reservation verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, limit: usize)
            requires old(v).len() < limit,
            ensures final(v).len() == old(v).len() + 1,
            resources peak(memory) <= 16,
        { v.push(1); }
        fn fill(v: &mut Vec<u32>, limit: usize)
            requires old(v).len() <= limit,
            ensures final(v).len() == limit,
            resources peak(memory) <= 32,
        {
            while v.len() < limit
                invariant v.len() <= limit,
                decreases limit - v.len(),
            { append(v, limit); }
        }
        fn run(n: usize) requires n <= 8, resources peak(memory) <= 64 + 4 * n {
            let mut v = Vec::<u32>::with_capacity(n);
            fill(&mut v, n);
            assert(v.len() == n);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inferred_candidates_must_be_proved_in_body verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, limit: usize)
            requires old(v).len() < limit || limit == 0,
            resources peak(memory) <= 16,
        { v.push(1); }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}
