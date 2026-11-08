use crate::common::*;

test_verify_one_file! {
    #[test] read_only_vector_parameter verus_code! {
        use vstd::prelude::*;
        fn read(v: &Vec<u32>) -> (n: usize)
            ensures n == v.len(),
            mem_peak <= 16,
        { v.len() }
        fn run() mem_peak <= 48 {
            let mut v = Vec::<u32>::with_capacity(2);
            v.push(1);
            let n = read(&v);
            assert(n == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] append_helper_preserves_contents_and_reservation verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn append(v: &mut Vec<u32>, cap: usize, value: u32)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(value),
            mem_peak <= 20,
        { v.push(value); }
        fn run() mem_peak <= 52 {
            let mut v = Vec::<u32>::with_capacity(2);
            append(&mut v, 2, 10);
            append(&mut v, 2, 20);
            assert(v.len() == 2 && v[0] == 10 && v[1] == 20);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_mutable_reborrow verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn append(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(7),
            mem_peak <= 16,
        { v.push(7); }
        #[verifier::memory_capacity(v, cap)]
        fn forward(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(7),
            mem_peak <= 32,
        { append(v, cap); }
        fn run() mem_peak <= 60 {
            let mut v = Vec::<u32>::with_capacity(1);
            forward(&mut v, 1);
            assert(v[0] == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] insufficient_call_reservation verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn append(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            mem_peak <= 16,
        { v.push(1); }
        fn run() mem_peak <= 100 {
            let mut v = Vec::<u32>::with_capacity(1);
            append(&mut v, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] borrowed_push_requires_room verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn append(v: &mut Vec<u32>, cap: usize) mem_peak <= 16 { v.push(1); }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] borrowed_push_requires_capacity_contract verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>) mem_peak <= 8 { v.push(1); }
    } => Err(err) => assert_vir_error_msg(err, "without a capacity contract")
}

test_verify_one_file! {
    #[test] borrowed_pop_and_index_preserve_backing_storage verus_code! {
        use vstd::prelude::*;
        fn update(v: &mut Vec<u32>)
            requires old(v).len() == 2,
            ensures final(v).len() == 1 && final(v)[0] == 9,
            mem_peak <= 8,
        { v[0] = 9; v.pop(); }
        fn run() mem_peak <= 40 {
            let mut v = Vec::<u32>::with_capacity(2);
            v.push(1); v.push(2);
            update(&mut v);
            v.push(3);
            assert(v[0] == 9 && v[1] == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_capacity_through_loop_and_shared_reborrow verus_code! {
        use vstd::prelude::*;
        fn count(v: &Vec<u32>) -> (n: usize)
            ensures n == v.len(), mem_peak <= 16,
        { v.len() }
        #[verifier::memory_capacity(v, cap)]
        fn fill(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() <= cap,
            ensures final(v).len() == cap,
            mem_peak <= 40,
        {
            while v.len() < cap
                invariant v.len() <= cap,
                decreases cap - v.len(),
            { v.push(5); }
            let n = count(&*v);
            assert(n == cap);
        }
        fn run(cap: usize) requires cap <= 4,
            mem_peak <= mem_size(cap) + mem_size(Vec<u32>) + cap * mem_size(u32) + 40,
        {
            let mut v = Vec::<u32>::with_capacity(cap);
            fill(&mut v, cap);
            assert(v.len() == cap);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] smaller_contract_does_not_shrink_callers_reservation verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 1)]
        fn first(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            ensures final(v).len() == 1,
            mem_peak <= 8,
        { v.push(1); }
        fn run() mem_peak <= 40 {
            let mut v = Vec::<u32>::with_capacity(2);
            first(&mut v);
            v.push(2);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] owned_vector_capacity_contract verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn append(mut v: Vec<u32>, cap: usize) -> (result: Vec<u32>)
            requires v.len() < cap,
            ensures result@ == v@.push(3),
            mem_peak <= 32,
        { v.push(3); v }
        fn run() mem_peak <= 64 {
            let v = Vec::<u32>::with_capacity(2);
            let mut v = append(v, 1);
            v.push(4);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] zero_size_elements_still_need_reserved_room verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 0)]
        fn push(v: &mut Vec<()>) mem_peak <= 8 { v.push(()); }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] unused_capacity_precondition_is_enforced verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 2)]
        fn helper(v: &Vec<u32>) mem_peak <= 8 {}
        fn run() mem_peak <= 100 {
            let v = Vec::<u32>::with_capacity(1);
            helper(&v);
        }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] borrowed_vector_growth_remains_unsupported verus_code! {
        use vstd::prelude::*;
        fn grow(v: &mut Vec<u32>) mem_peak <= 100 { v.reserve(1); }
    } => Err(err) => assert_vir_error_msg(err, "does not support")
}

test_verify_one_file! {
    #[test] borrowed_vector_replacement_remains_unsupported verus_code! {
        use vstd::prelude::*;
        fn replace(v: &mut Vec<u32>) mem_peak <= 100 { *v = Vec::<u32>::new(); }
    } => Err(err) => assert_vir_error_msg(err, "reassignment of heap owners")
}

test_verify_one_file! {
    #[test] mutable_borrow_binding_cannot_reuse_capacity_contract verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 2)]
        fn helper(mut v: &mut Vec<u32>) mem_peak <= 100 {}
    } => Err(err) => assert_vir_error_msg(err, "mutable bindings for borrowed vector parameters")
}

test_verify_one_file! {
    #[test] duplicate_capacity_rejected verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 1)]
        #[verifier::memory_capacity(v, 2)]
        fn helper(v: &Vec<u32>) mem_peak <= 8 {}
    } => Err(err) => assert_vir_error_msg(err, "duplicate memory_capacity")
}

test_verify_one_file! {
    #[test] capacity_requires_vector_parameter verus_code! {
        #[verifier::memory_capacity(n, 1)]
        fn helper(n: usize) mem_peak <= 8 {}
    } => Err(err) => assert_vir_error_msg(err, "executable vector parameter")
}

test_verify_one_file! {
    #[test] mutable_capacity_input_rejected verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, cap)]
        fn helper(v: &Vec<u32>, mut cap: usize) mem_peak <= 16 {}
    } => Err(err) => assert_vir_error_msg(err, "immutable")
}

#[test]
fn borrowed_vector_example_compiles() {
    crate::verify_one_file(
        "vector_helpers",
        include_str!("../../../../../examples/resource/memory/vector_helpers.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] borrowed_call_still_counts_callers_allocation verus_code! {
        use vstd::prelude::*;
        fn inspect(v: &Vec<u32>) mem_peak <= 8 {}
        fn run() mem_peak <= 39 {
            let v = Vec::<u32>::with_capacity(2);
            inspect(&v);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 40 bytes exceeds budget 39 bytes")
}

test_verify_one_file! {
    #[test] unknown_capacity_cannot_be_forwarded_as_known verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 1)]
        fn inspect(v: &Vec<u32>) mem_peak <= 8 {}
        fn forward(v: &Vec<u32>) mem_peak <= 16 { inspect(v); }
    } => Err(err) => assert_vir_error_msg(err, "without a capacity contract")
}

test_verify_one_file! {
    #[test] local_borrow_alias_rejected verus_code! {
        use vstd::prelude::*;
        fn inspect(v: &Vec<u32>) mem_peak <= 8 {}
        fn run() mem_peak <= 100 {
            let v = Vec::<u32>::with_capacity(1);
            let alias = &v;
            inspect(alias);
        }
    } => Err(err) => assert_vir_error_msg(err, "named owner or parameter")
}

test_verify_one_file! {
    #[test] capacity_contract_without_budget_rejected verus_code! {
        use vstd::prelude::*;
        #[verifier::memory_capacity(v, 1)]
        fn helper(v: &Vec<u32>) {}
    } => Err(err) => assert_vir_error_msg(err, "memory_capacity requires a mem_peak contract")
}
