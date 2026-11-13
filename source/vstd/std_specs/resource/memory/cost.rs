//! Memory-kind costs and additive charge bounds for allocation forests.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::forest::{Record, contains, nonruntime, prefix, runtime, subtree, well_formed, without};
#[cfg(verus_keep_ghost)]
use super::ranges::{repeat, reverse_children, take_children};
#[cfg(verus_keep_ghost)]
use super::selection::{contains_runtime, inspect, select_runtime};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// An empty forest contributes no charge in any memory kind.
pub broadcast proof fn cost_empty(kind: int)
    ensures
        #[trigger] cost(Seq::empty(), kind) == 0,
{
    reveal(cost);
}

/// The two structural classes partition the charge without geometry assumptions.
pub proof fn cost_runtime_partition(memory: Seq<Record>, kind: int)
    ensures
        cost(memory, kind) == cost(runtime(memory), kind) + cost(nonruntime(memory), kind),
        !contains(runtime(memory), Seq::empty()),
        forall|index: int|
            index >= 0 ==> #[trigger] subtree(runtime(memory), seq![index]) == subtree(
                memory,
                seq![index],
            ),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        cost_runtime_partition(memory.drop_last(), kind);
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            cost_push(runtime(memory.drop_last()), memory.last(), kind);
        } else {
            cost_push(nonruntime(memory.drop_last()), memory.last(), kind);
        }
    }
    contains_runtime(memory, Seq::empty());
    assert forall|index: int| index >= 0 implies #[trigger] subtree(runtime(memory), seq![index])
        == subtree(memory, seq![index]) by {
        select_runtime(memory, seq![index]);
    }
}

// Keep recursive inspection inside the algebra's proofs. Eager unfolding at
// callers introduces large families of Seq indices after nested forest joins.
/// Sum one memory kind. Inline handles belong to their enclosing
/// source value or allocation and do not appear as additional records.
#[verifier::opaque]
pub open spec fn cost(memory: Seq<Record>, kind: int) -> int
    decreases memory.len(),
{
    if memory.len() == 0 {
        0
    } else {
        cost(memory.drop_last(), kind) + if memory.last().kind == kind {
            memory.last().bytes
        } else {
            0
        }
    }
}

/// Range costs use prefix cuts; indexed views use the inverse range map.
/// Neither fact requires expanding every transferred record at a call site.
pub proof fn reverse_children_cost(memory: Seq<Record>, start: int, end: int, base: int)
    ensures
        cost(reverse_children(memory, start, end, base), 0) == if start <= end {
            cost(take_children(memory, end), 0) - cost(take_children(memory, start), 0)
        } else {
            0
        },
    decreases memory.len(),
{
    reveal_with_fuel(reverse_children, 2);
    reveal_with_fuel(take_children, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        reverse_children_cost(memory.drop_last(), start, end, base);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] >= 0 {
            if value.path[0] < end {
                let before = take_children(memory.drop_last(), end);
                assert(before.push(value).drop_last() =~= before);
                cost_push(before, value, 0);
            }
            if value.path[0] < start {
                let before = take_children(memory.drop_last(), start);
                assert(before.push(value).drop_last() =~= before);
                cost_push(before, value, 0);
            }
            if start <= value.path[0] < end {
                let before = reverse_children(memory.drop_last(), start, end, base);
                let mapped = Record {
                    path: value.path.update(0, base + end - 1 - value.path[0]),
                    ..value
                };
                assert(before.push(mapped).drop_last() =~= before);
                cost_push(before, mapped, 0);
            }
        }
    }
}

/// Quantitative views of a repeated region stay available after range cuts.
pub broadcast proof fn cost_repeat(child: Seq<Record>, start: int, count: int, kind: int)
    requires
        count >= 0,
    ensures
        #[trigger] cost(repeat(child, start, count), kind) == count * cost(child, kind),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    if count > 0 {
        cost_repeat(child, start, count - 1, kind);
        let before = repeat(child, start, count - 1);
        let path = seq![start + count - 1];
        cost_prefix(child, path, kind);
        cost_add(before, prefix(child, path), kind);
        assert(cost(repeat(child, start, count), kind) == cost(before, kind) + cost(child, kind));
        assert((count - 1) * cost(child, kind) + cost(child, kind) == count * cost(child, kind))
            by (nonlinear_arith);
        assert(cost(repeat(child, start, count), kind) == count * cost(child, kind));
    } else {
        cost_empty(kind);
        assert(count * cost(child, kind) == 0) by (nonlinear_arith)
            requires
                count == 0,
        ;
    }
}

/// Joining disjoint owners adds their footprints.
pub broadcast proof fn cost_add(left: Seq<Record>, right: Seq<Record>, kind: int)
    ensures
        #[trigger] cost(left + right, kind) == cost(left, kind) + cost(right, kind),
    decreases right.len(),
{
    reveal_with_fuel(cost, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        cost_add(left, right.drop_last(), kind);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Appending one allocation adds its charge exactly once.
pub broadcast proof fn cost_push(memory: Seq<Record>, record: Record, kind: int)
    ensures
        #[trigger] cost(memory.push(record), kind) == cost(memory, kind) + if record.kind == kind {
            record.bytes
        } else {
            0
        },
{
    reveal(cost);
    assert(memory.push(record).drop_last() =~= memory);
}

/// Moving an owner underneath another value changes paths, not charges.
pub broadcast proof fn cost_prefix(memory: Seq<Record>, path: Seq<int>, kind: int)
    ensures
        #[trigger] cost(prefix(memory, path), kind) == cost(memory, kind),
    decreases memory.len(),
{
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        cost_prefix(memory.drop_last(), path, kind);
        cost_push(
            prefix(memory.drop_last(), path),
            Record { path: path + memory.last().path, ..memory.last() },
            kind,
        );
    }
}

/// Extraction partitions storage exactly; it never copies or loses a charge.
pub proof fn cost_partition(memory: Seq<Record>, path: Seq<int>, kind: int)
    ensures
        cost(memory, kind) == cost(subtree(memory, path), kind) + cost(without(memory, path), kind),
        well_formed(memory) && kind == 0 ==> cost(subtree(memory, path), kind) >= 0 && cost(
            without(memory, path),
            kind,
        ) >= 0,
    decreases memory.len(),
{
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        cost_partition(memory.drop_last(), path, kind);
        if path.is_prefix_of(memory.last().path) {
            cost_push(
                subtree(memory.drop_last(), path),
                Record { path: memory.last().path.skip(path.len() as int), ..memory.last() },
                kind,
            );
        } else {
            cost_push(without(memory.drop_last(), path), memory.last(), kind);
        }
    }
    if well_formed(memory) && kind == 0 {
        inspect(memory, path);
        inspect(subtree(memory, path), Seq::empty());
        inspect(without(memory, path), Seq::empty());
    }
}

} // verus!
