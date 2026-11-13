//! Ordered child ranges, repetition, reversal, shifting, and retention.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::blocks::block_bounds;
#[cfg(verus_keep_ghost)]
use super::cost::{cost, cost_repeat};
#[cfg(verus_keep_ghost)]
use super::forest::{
    Record, descendants, nonruntime, prefix, runtime, runtime_add, runtime_prefix, runtime_push,
    subtree, well_formed, well_formed_add, well_formed_prefix, without,
};
#[cfg(verus_keep_ghost)]
use super::selection::{
    descendants_add, descendants_prefix, descendants_push, select_add, select_empty, select_prefix,
    select_push, singleton_prefix, slot_prefix,
};
#[cfg(verus_keep_ghost)]
use super::views::{request_path, view_requested};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Move a runtime interval to consecutive destination indices in reverse order.
/// The nested descriptors and their byte extents are preserved independently of
/// the element layout; repeated pops followed by pushes induce this map.
#[verifier::opaque]
pub open spec fn reverse_children(memory: Seq<Record>, start: int, end: int, base: int) -> Seq<
    Record,
>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = reverse_children(memory.drop_last(), start, end, base);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] && start <= value.path[0] < end {
            before.push(
                Record { path: value.path.update(0, base + end - 1 - value.path[0]), ..value },
            )
        } else {
            before
        }
    }
}

/// Range transfer preserves validity and never invents allocation bytes.
pub proof fn reverse_children_facts(memory: Seq<Record>, start: int, end: int, base: int)
    requires
        well_formed(memory),
        base >= 0,
    ensures
        well_formed(reverse_children(memory, start, end, base)),
        0 <= cost(reverse_children(memory, start, end, base), 0) <= cost(memory, 0),
        runtime(reverse_children(memory, start, end, base)) == reverse_children(
            memory,
            start,
            end,
            base,
        ),
        nonruntime(reverse_children(memory, start, end, base)) == Seq::<Record>::empty(),
        descendants(reverse_children(memory, start, end, base)) == reverse_children(
            memory,
            start,
            end,
            base,
        ),
    decreases memory.len(),
{
    reveal_with_fuel(reverse_children, 2);
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        reverse_children_facts(memory.drop_last(), start, end, base);
        let before = reverse_children(memory.drop_last(), start, end, base);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] && start <= value.path[0] < end {
            let mapped = Record {
                path: value.path.update(0, base + end - 1 - value.path[0]),
                ..value
            };
            assert(before.push(mapped).drop_last() =~= before);
            runtime_push(before, mapped);
            descendants_push(before, mapped);
        }
    }
}

/// Select a transferred child through the inverse range map, independently of
/// the number of iterations and the child's nested allocation layout.
pub proof fn reverse_children_views(memory: Seq<Record>, start: int, end: int, base: int)
    requires
        base >= 0,
    ensures
        forall|index: int|
            #![trigger view_requested(reverse_children(memory, start, end, base), index), subtree(reverse_children(memory, start, end, base), seq![index])]
            view_requested(reverse_children(memory, start, end, base), index) ==> (subtree(
                reverse_children(memory, start, end, base),
                seq![index],
            ) == if base + end - 1 - index >= 0 && start <= base + end - 1 - index < end {
                subtree(memory, seq![base + end - 1 - index])
            } else {
                Seq::<Record>::empty()
            }),
    decreases memory.len(),
{
    reveal_with_fuel(reverse_children, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        reverse_children_views(memory.drop_last(), start, end, base);
    }
    assert forall|index: int|
        #![trigger view_requested(reverse_children(memory, start, end, base), index), subtree(reverse_children(memory, start, end, base), seq![index])]
        view_requested(reverse_children(memory, start, end, base), index) ==> (subtree(
            reverse_children(memory, start, end, base),
            seq![index],
        ) == if base + end - 1 - index >= 0 && start <= base + end - 1 - index < end {
            subtree(memory, seq![base + end - 1 - index])
        } else {
            Seq::<Record>::empty()
        }) by {
        if memory.len() > 0 {
            request_path(reverse_children(memory.drop_last(), start, end, base), seq![index]);
            let value = memory.last();
            let original = base + end - 1 - index;
            assert(memory.drop_last().push(value) =~= memory);
            select_push(memory.drop_last(), value, seq![original]);
            slot_prefix(original, value.path);
            assert(subtree(reverse_children(memory.drop_last(), start, end, base), seq![index])
                == if original >= 0 && start <= original < end {
                subtree(memory.drop_last(), seq![original])
            } else {
                Seq::<Record>::empty()
            });
            if value.path.len() > 0 && 0 <= value.path[0] && start <= value.path[0] < end {
                let before = reverse_children(memory.drop_last(), start, end, base);
                let mapped = Record {
                    path: value.path.update(0, base + end - 1 - value.path[0]),
                    ..value
                };
                assert(before.push(mapped).drop_last() =~= before);
                select_push(before, mapped, seq![index]);
                slot_prefix(index, mapped.path);
                assert(mapped.path.skip(1) =~= value.path.skip(1));
            }
        }
    }
}

/// Expose finite caller descriptors without unfolding recursive range transfers.
pub broadcast proof fn reverse_children_push(
    memory: Seq<Record>,
    value: Record,
    start: int,
    end: int,
    base: int,
)
    ensures
        #[trigger] reverse_children(memory.push(value), start, end, base) == if value.path.len() > 0
            && 0 <= value.path[0] && start <= value.path[0] < end {
            reverse_children(memory, start, end, base).push(
                Record { path: value.path.update(0, base + end - 1 - value.path[0]), ..value },
            )
        } else {
            reverse_children(memory, start, end, base)
        },
{
    reveal_with_fuel(reverse_children, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Range transfer distributes over disjoint contributions to a forest.
pub broadcast proof fn reverse_children_add(
    left: Seq<Record>,
    right: Seq<Record>,
    start: int,
    end: int,
    base: int,
)
    ensures
        #[trigger] reverse_children(left + right, start, end, base) == reverse_children(
            left,
            start,
            end,
            base,
        ) + reverse_children(right, start, end, base),
    decreases right.len(),
{
    reveal_with_fuel(reverse_children, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        reverse_children_add(left, right.drop_last(), start, end, base);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A selected child keeps its entire nested forest at the mapped destination.
pub broadcast proof fn reverse_children_prefix(
    memory: Seq<Record>,
    path: Seq<int>,
    start: int,
    end: int,
    base: int,
)
    requires
        path.len() > 0,
    ensures
        #[trigger] reverse_children(prefix(memory, path), start, end, base) == if 0 <= path[0]
            && start <= path[0] < end {
            prefix(memory, path.update(0, base + end - 1 - path[0]))
        } else {
            Seq::<Record>::empty()
        },
    decreases memory.len(),
{
    reveal_with_fuel(reverse_children, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        reverse_children_prefix(memory.drop_last(), path, start, end, base);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
        assert((path + memory.last().path).update(0, base + end - 1 - path[0]) =~= path.update(
            0,
            base + end - 1 - path[0],
        ) + memory.last().path);
    }
}

/// Repeated children keep their full nested forest at consecutive indices.
/// Callers use `repeat_facts` to avoid recursively expanding a whole region.
#[verifier::opaque]
pub open spec fn repeat(child: Seq<Record>, start: int, count: int) -> Seq<Record>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        repeat(child, start, count - 1) + prefix(child, seq![start + count - 1])
    }
}

/// A repeated region has a uniform per-element footprint and exact index views.
pub proof fn repeat_facts(child: Seq<Record>, start: int, count: int)
    requires
        well_formed(child),
        start >= 0,
        count >= 0,
    ensures
        well_formed(repeat(child, start, count)),
        cost(repeat(child, start, count), 0) == count * cost(child, 0),
        runtime(repeat(child, start, count)) == repeat(child, start, count),
        nonruntime(repeat(child, start, count)) == Seq::<Record>::empty(),
        descendants(repeat(child, start, count)) == repeat(child, start, count),
        forall|index: int| #[trigger]
            subtree(repeat(child, start, count), seq![index]) == if start <= index < start + count {
                child
            } else {
                Seq::<Record>::empty()
            },
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    cost_repeat(child, start, count, 0);
    if count > 0 {
        repeat_facts(child, start, count - 1);
        let before = repeat(child, start, count - 1);
        let path = seq![start + count - 1];
        let next = prefix(child, path);
        well_formed_prefix(child, path);
        well_formed_add(before, next);
        runtime_add(before, next);
        runtime_prefix(child, path);
        descendants_add(before, next);
        descendants_prefix(child, path);
    }
    assert forall|index: int| #[trigger]
        subtree(repeat(child, start, count), seq![index]) == if start <= index < start + count {
            child
        } else {
            Seq::<Record>::empty()
        } by {
        if count > 0 {
            let before = repeat(child, start, count - 1);
            let path = seq![start + count - 1];
            select_add(before, prefix(child, path), seq![index]);
            select_prefix(child, path, seq![index]);
            singleton_prefix(start + count - 1, index);
            singleton_prefix(index, start + count - 1);
        } else {
            select_empty(seq![index]);
        }
    }
}

/// Translate runtime indices without changing allocation descriptors or costs.
#[verifier::opaque]
pub open spec fn shift_children(memory: Seq<Record>, base: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let value = memory.last();
        let mapped = if value.path.len() > 0 && value.path[0] >= 0 {
            Record { path: value.path.update(0, value.path[0] + base), ..value }
        } else {
            value
        };
        shift_children(memory.drop_last(), base).push(mapped)
    }
}

/// Shifts preserve charges exactly, independently of child layout.
pub proof fn shift_children_facts(memory: Seq<Record>, base: int)
    requires
        well_formed(memory),
        base >= 0,
    ensures
        well_formed(shift_children(memory, base)),
        cost(shift_children(memory, base), 0) == cost(memory, 0),
        runtime(shift_children(memory, base)) == shift_children(runtime(memory), base),
        nonruntime(shift_children(memory, base)) == nonruntime(memory),
        descendants(shift_children(memory, base)) == shift_children(descendants(memory), base),
    decreases memory.len(),
{
    reveal_with_fuel(shift_children, 2);
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(descendants, 2);
    if memory.len() > 0 {
        shift_children_facts(memory.drop_last(), base);
        let value = memory.last();
        let mapped = if value.path.len() > 0 && value.path[0] >= 0 {
            Record { path: value.path.update(0, value.path[0] + base), ..value }
        } else {
            value
        };
        let before = shift_children(memory.drop_last(), base);
        assert(before.push(mapped).drop_last() =~= before);
        runtime_push(memory.drop_last(), value);
        runtime_push(before, mapped);
        descendants_push(memory.drop_last(), value);
        descendants_push(before, mapped);
        if value.path.len() > 0 && value.path[0] >= 0 {
            assert(mapped.path[0] >= 0);
            let filtered = runtime(memory.drop_last());
            assert(filtered.push(value).drop_last() =~= filtered);
            assert(shift_children(filtered.push(value), base) == shift_children(
                filtered,
                base,
            ).push(mapped));
        }
        if value.path.len() > 0 {
            let filtered = descendants(memory.drop_last());
            assert(filtered.push(value).drop_last() =~= filtered);
            assert(shift_children(filtered.push(value), base) == shift_children(
                filtered,
                base,
            ).push(mapped));
        }
    }
}

/// An indexed view follows the inverse translation of its runtime slot.
pub proof fn shift_children_select(memory: Seq<Record>, width: int, base: int, index: int)
    requires
        block_bounds(memory, width),
        base >= 0,
    ensures
        subtree(shift_children(memory, base), seq![index]) == subtree(memory, seq![index - base]),
    decreases memory.len(),
{
    reveal_with_fuel(shift_children, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        shift_children_select(memory.drop_last(), width, base, index);
        let before = shift_children(memory.drop_last(), base);
        let value = memory.last();
        let mapped = Record { path: value.path.update(0, value.path[0] + base), ..value };
        assert(before.push(mapped).drop_last() =~= before);
        slot_prefix(index, mapped.path);
        slot_prefix(index - base, value.path);
        assert(mapped.path.skip(1) =~= value.path.skip(1));
    }
}

/// Keep the existing runtime children before a logical end index.
pub open spec fn take_children(memory: Seq<Record>, length: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = take_children(memory.drop_last(), length);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] < length {
            before.push(value)
        } else {
            before
        }
    }
}

/// Retaining a range never increases storage and preserves its child views.
/// An empty range releases every child without unfolding individual descriptors.
pub proof fn take_children_facts(memory: Seq<Record>, length: int)
    requires
        well_formed(memory),
    ensures
        well_formed(take_children(memory, length)),
        0 <= cost(take_children(memory, length), 0) <= cost(memory, 0),
        runtime(take_children(memory, length)) == take_children(memory, length),
        nonruntime(take_children(memory, length)) == Seq::<Record>::empty(),
        descendants(take_children(memory, length)) == take_children(memory, length),
        length <= 0 ==> take_children(memory, length) == Seq::<Record>::empty(),
        forall|index: int| #[trigger]
            subtree(take_children(memory, length), seq![index]) == if 0 <= index < length {
                subtree(memory, seq![index])
            } else {
                Seq::<Record>::empty()
            },
    decreases memory.len(),
{
    reveal_with_fuel(take_children, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        take_children_facts(memory.drop_last(), length);
        let before = take_children(memory.drop_last(), length);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] < length {
            assert(before.push(value).drop_last() =~= before);
            runtime_push(before, value);
            descendants_push(before, value);
        }
        assert forall|index: int| #[trigger]
            subtree(take_children(memory, length), seq![index]) == if 0 <= index < length {
                subtree(memory, seq![index])
            } else {
                Seq::<Record>::empty()
            } by {
            select_push(memory.drop_last(), value, seq![index]);
            if value.path.len() > 0 && 0 <= value.path[0] < length {
                select_push(before, value, seq![index]);
            }
            slot_prefix(index, value.path);
        }
    }
}

/// Retaining a prefix of an empty forest yields no allocation descriptors.
pub broadcast proof fn take_children_empty(length: int)
    ensures
        #[trigger] take_children(Seq::<Record>::empty(), length) == Seq::<Record>::empty(),
{
    reveal(take_children);
}

/// Retention ignores fixed descriptors and commutes with runtime filtering.
pub broadcast proof fn take_children_runtime(memory: Seq<Record>, length: int)
    ensures
        #[trigger] take_children(runtime(memory), length) == take_children(memory, length),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(take_children, 2);
    if memory.len() > 0 {
        take_children_runtime(memory.drop_last(), length);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
        }
    }
}

/// A container root descriptor never belongs to its runtime child prefix.
pub broadcast proof fn take_children_root(memory: Seq<Record>, value: Record, length: int)
    requires
        value.path.len() == 0,
    ensures
        #[trigger] take_children(memory.push(value), length) == take_children(memory, length),
{
    reveal_with_fuel(take_children, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Range retention distributes over independently composed allocation forests.
pub broadcast proof fn take_children_add(left: Seq<Record>, right: Seq<Record>, length: int)
    ensures
        #[trigger] take_children(left + right, length) == take_children(left, length)
            + take_children(right, length),
    decreases right.len(),
{
    reveal_with_fuel(take_children, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        take_children_add(left, right.drop_last(), length);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A complete child is retained or released according to its runtime index.
pub broadcast proof fn take_children_prefix(memory: Seq<Record>, path: Seq<int>, length: int)
    requires
        path.len() > 0,
    ensures
        #[trigger] take_children(prefix(memory, path), length) == if 0 <= path[0] < length {
            prefix(memory, path)
        } else {
            Seq::<Record>::empty()
        },
    decreases memory.len(),
{
    reveal_with_fuel(take_children, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        take_children_prefix(memory.drop_last(), path, length);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Shrinking a repeated region keeps the same complete child descriptors.
pub broadcast proof fn take_children_repeat(child: Seq<Record>, start: int, count: int, length: int)
    requires
        start >= 0,
        count >= 0,
    ensures
        #[trigger] take_children(repeat(child, start, count), length) == repeat(
            child,
            start,
            if length <= start {
                0
            } else if length >= start + count {
                count
            } else {
                length - start
            },
        ),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    if count > 0 {
        let before = repeat(child, start, count - 1);
        let path = seq![start + count - 1];
        take_children_add(before, prefix(child, path), length);
        take_children_prefix(child, path, length);
        take_children_repeat(child, start, count - 1, length);
    }
}

} // verus!
