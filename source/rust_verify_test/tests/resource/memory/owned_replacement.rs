//! Replacement retires original input regions without absorbing new allocations.

use super::support::{rejects, verifies};

#[test]
fn replacement_retires_only_the_displaced_input_before_later_extraction() {
    let code = "fn take(mut v: Vec<Vec<u32>>) -> Vec<u32>
        requires v.len() == 2,
        resources peak(memory) <= 280 {
            let empty = Vec::<u32>::new(); v[0] = empty;
            let empty = Vec::<u32>::new(); v[0] = empty;
            { let scratch = [0u8;256]; }
            let removed = v.remove(0); drop(removed);
            let child = v.pop().unwrap(); drop(v);
            child
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(16); v.push(a);
            let b = Vec::<u32>::with_capacity(32); v.push(b);
            let child = take(v);
        }";
    // Before extraction: 24-byte handle, 48-byte backing, 128-byte survivor,
    // and 256-byte workspace. The displaced 64 bytes must already be gone;
    // replacing the same index again must not retire the survivor instead.
    verifies("retired_input", &code.replace("BOUND", "456"));
    rejects("retired_input_short", &code.replace("BOUND", "455"), "memory budget exceeded");
}

#[test]
fn replacement_allocations_survive_remove_and_pop_without_original_bytes() {
    for (name, index, extraction) in [("remove", 0, "v.remove(0)"), ("pop", 1, "v.pop().unwrap()")]
    {
        let code = format!(
            "fn take(mut v: Vec<Vec<u32>>) -> (r: Vec<u32>)
                requires v.len() == 2,
                ensures r.len() == 0,
                resources peak(memory) <= 128 {{
                    let first = Vec::<u32>::with_capacity(4); v[{index}] = first;
                    let second = Vec::<u32>::with_capacity(8); v[{index}] = second;
                    {extraction}
                }}
                fn f() resources peak(memory) <= BOUND {{
                    let mut v = Vec::<Vec<u32>>::with_capacity(2);
                    let a = Vec::<u32>::with_capacity(16); v.push(a);
                    let b = Vec::<u32>::with_capacity(32); v.push(b);
                    let mut child = take(v); child.push(7);
                    let scratch = [0u8;512];
                }}"
        );
        // The returned vector owns only the final 32-byte replacement buffer.
        verifies(name, &code.replace("BOUND", "568"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "567"), "memory budget exceeded");
    }
}

#[test]
fn replacement_keeps_old_and_new_allocations_live_during_rhs_evaluation() {
    let code = "fn replace(mut v: Vec<Box<[u8;32]>>)
        requires v.len() == 1,
        resources peak(memory) <= 88 {
            v[0] = Box::new([0u8;32]); drop(v);
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let child = Box::new([0u8;32]); v.push(child); replace(v);
        }";
    // At allocation: v's 24-byte handle, its original 40 heap bytes, the
    // replacement's 32 heap bytes, and the 32-byte array constructor operand.
    verifies("replacement_overlap", &code.replace("BOUND", "128"));
    rejects("replacement_overlap_short", &code.replace("BOUND", "127"), "memory budget exceeded");
}

#[test]
fn replacing_a_nested_field_preserves_other_fixed_and_runtime_regions() {
    let code = "struct Child { data: Vec<u32>, tag: Box<[u8;64]>, }
        fn take(mut v: Box<Vec<Vec<Child>>>) -> Box<[u8;64]>
            requires v.len() == 1, v[0].len() == 1,
            resources peak(memory) <= 544 {
                let empty = Vec::<u32>::new(); v[0][0].data = empty;
                let child = v[0].remove(0); drop(v);
                { let scratch = [0u8;512]; }
                child.tag
            }
        fn f() resources peak(memory) <= BOUND {
            let mut rows = Vec::<Vec<Child>>::with_capacity(1);
            let mut row = Vec::<Child>::with_capacity(1);
            let child = Child {
                data: Vec::<u32>::with_capacity(16), tag: Box::new([0u8;64]),
            };
            row.push(child); rows.push(row);
            let v = Box::new(rows); let result = take(v);
        }";
    verifies("nested_field", &code.replace("BOUND", "608"));
    rejects("nested_field_short", &code.replace("BOUND", "607"), "memory budget exceeded");
}

#[test]
fn leaf_helper_replacement_retires_the_same_original_subtree() {
    let code = "struct Child { data: Option<Box<[u8;32]>>, tag: Box<[u8;64]>, }
        fn clear(p: &mut Child, empty: Option<Box<[u8;32]>>)
            resources peak(memory) <= 17 { p.data = empty; }
        fn take(mut v: Vec<Child>) -> Box<[u8;64]>
            requires v.len() == 1,
            resources peak(memory) <= 273 {
                let empty: Option<Box<[u8;32]>> = None; clear(&mut v[0], empty);
                let child = v.pop().unwrap(); drop(v);
                { let scratch = [0u8;256]; }
                child.tag
            }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Child>::with_capacity(1);
            let child = Child {
                data: Some(Box::new([0u8;32])), tag: Box::new([0u8;64]),
            };
            v.push(child); let result = take(v);
        }";
    verifies("leaf_replacement", &code.replace("BOUND", "337"));
    rejects("leaf_replacement_short", &code.replace("BOUND", "336"), "memory budget exceeded");
}
