use crate::common::*;

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
