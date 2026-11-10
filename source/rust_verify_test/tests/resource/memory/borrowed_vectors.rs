use crate::common::*;

test_verify_one_file! {
    #[test] read_only_vector_parameter verus_code! {
        use vstd::prelude::*;
        fn read(v: &Vec<u32>) -> (n: usize)
            ensures n == v.len(),
            resources peak(memory) <= 16,
        { v.len() }
        fn run() resources peak(memory) <= 48 {
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
        fn append(v: &mut Vec<u32>, cap: usize, value: u32)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(value),
            resources peak(memory) <= 20,
        { v.push(value); }
        fn run() resources peak(memory) <= 52 {
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
        fn append(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(7),
            resources peak(memory) <= 16,
        { v.push(7); }
        fn forward(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            ensures final(v)@ == old(v)@.push(7),
            resources peak(memory) <= 32,
        { append(v, cap); }
        fn run() resources peak(memory) <= 60 {
            let mut v = Vec::<u32>::with_capacity(1);
            forward(&mut v, 1);
            assert(v[0] == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] insufficient_call_reservation verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() < cap,
            resources peak(memory) <= 16,
        { v.push(1); }
        fn run() resources peak(memory) <= 100 {
            let mut v = Vec::<u32>::with_capacity(1);
            append(&mut v, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

test_verify_one_file! {
    #[test] borrowed_push_requires_room verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>, cap: usize) resources peak(memory) <= 16 { v.push(1); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] borrowed_push_requires_growth_budget verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>) resources peak(memory) <= 8 { v.push(1); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] borrowed_pop_and_index_preserve_backing_storage verus_code! {
        use vstd::prelude::*;
        fn update(v: &mut Vec<u32>)
            requires old(v).len() == 2,
            ensures final(v).len() == 1 && final(v)[0] == 9,
            resources peak(memory) <= 8,
        { v[0] = 9; v.pop(); }
        fn run() resources peak(memory) <= 40 {
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
            ensures n == v.len(), resources peak(memory) <= 16,
        { v.len() }
        fn fill(v: &mut Vec<u32>, cap: usize)
            requires old(v).len() <= cap,
            ensures final(v).len() == cap,
            resources peak(memory) <= 40,
        {
            while v.len() < cap
                invariant v.len() <= cap,
                decreases cap - v.len(),
            { v.push(5); }
            let n = count(&*v);
            assert(n == cap);
        }
        fn run(cap: usize) requires cap <= 4,
            resources peak(memory) <= value_size(cap) + value_size(Vec<u32>) + cap * value_size(u32) + 40,
        {
            let mut v = Vec::<u32>::with_capacity(cap);
            fill(&mut v, cap);
            assert(v.len() == cap);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inferred_requirement_preserves_callers_reservation verus_code! {
        use vstd::prelude::*;
        fn first(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            ensures final(v).len() == 1,
            resources peak(memory) <= 8,
        { v.push(1); }
        fn run() resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::with_capacity(2);
            first(&mut v);
            v.push(2);
            assert(v.len() == 2);
        }
    } => Ok(())
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
    #[test] zero_size_elements_can_grow verus_code! {
        use vstd::prelude::*;
        fn push(v: &mut Vec<()>) resources peak(memory) <= 8 { v.push(()); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] read_only_helpers_need_no_reservation verus_code! {
        use vstd::prelude::*;
        fn helper(v: &Vec<u32>) resources peak(memory) <= 8 {}
        fn run() resources peak(memory) <= 100 {
            let v = Vec::<u32>::with_capacity(1);
            helper(&v);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_vector_growth_remains_unsupported verus_code! {
        use vstd::prelude::*;
        fn grow(v: &mut Vec<u32>) resources peak(memory) <= 100 { v.reserve(1); }
    } => Err(err) => assert_vir_error_msg(err, "does not support")
}

test_verify_one_file! {
    #[test] borrowed_vector_replacement_remains_unsupported verus_code! {
        use vstd::prelude::*;
        fn replace(v: &mut Vec<u32>) resources peak(memory) <= 100 { *v = Vec::<u32>::new(); }
    } => Err(err) => assert_vir_error_msg(err, "reassignment of heap owners")
}

test_verify_one_file! {
    #[test] mutable_borrow_binding_is_rejected verus_code! {
        use vstd::prelude::*;
        fn helper(mut v: &mut Vec<u32>) resources peak(memory) <= 100 {}
    } => Err(err) => assert_vir_error_msg(err, "mutable bindings for borrowed owner parameters")
}

#[test]
fn borrowed_vector_example_compiles() {
    crate::verify_one_file(
        "vector_helpers",
        include_str!("../../../../../examples/resource/memory/vectors/vector_helpers.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] borrowed_call_still_counts_callers_allocation verus_code! {
        use vstd::prelude::*;
        fn inspect(v: &Vec<u32>) resources peak(memory) <= 8 {}
        fn run() resources peak(memory) <= 39 {
            let v = Vec::<u32>::with_capacity(2);
            inspect(&v);
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] read_only_helpers_forward_unknown_capacity verus_code! {
        use vstd::prelude::*;
        fn inspect(v: &Vec<u32>) resources peak(memory) <= 8 {}
        fn forward(v: &Vec<u32>) resources peak(memory) <= 16 { inspect(v); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_borrow_alias_rejected verus_code! {
        use vstd::prelude::*;
        fn inspect(v: &Vec<u32>) resources peak(memory) <= 8 {}
        fn run() resources peak(memory) <= 100 {
            let v = Vec::<u32>::with_capacity(1);
            let alias = &v;
            inspect(alias);
        }
    } => Err(err) => assert_vir_error_msg(err, "aliased owner")
}

test_verify_one_file! {
    #[test] multiple_vector_requirements_are_inferred verus_code! {
        use vstd::prelude::*;
        fn append(a: &mut Vec<u32>, b: &mut Vec<u32>)
            requires old(a).len() == 0, old(b).len() == 0,
            ensures final(a).len() == 1, final(b).len() == 1,
            resources peak(memory) <= 16,
        { a.push(1); b.push(2); }
        fn run() resources peak(memory) <= 76 {
            let mut a = Vec::<u32>::with_capacity(1);
            let mut b = Vec::<u32>::with_capacity(2);
            append(&mut a, &mut b);
            assert(a.len() == 1 && b.len() == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inference_is_not_a_logical_assumption verus_code! {
        use vstd::prelude::*;
        fn helper(v: &Vec<u32>) resources peak(memory) <= 8 {
            assert(v.len() == 4);
        }
    } => Err(err) => assert_vir_error_msg(err, "assertion failed")
}
