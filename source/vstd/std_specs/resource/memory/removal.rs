//! Owning child removal, index shifting, and the remaining allocation forest.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::cost::{cost, cost_push};
#[cfg(verus_keep_ghost)]
use super::forest::{
    Record, descendants, lookup, nonruntime, prefix, runtime, subtree, well_formed,
};
#[cfg(verus_keep_ghost)]
use super::selection::{inspect, lookup_push, select_remove};
#[cfg(verus_keep_ghost)]
use super::views::view_requested;

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Remove one runtime child and shift the surviving indices with the container.
pub open spec fn remove_index(memory: Seq<Record>, index: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = remove_index(memory.drop_last(), index);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] == index {
            before
        } else if value.path.len() > 0 && value.path[0] > index {
            before.push(Record { path: value.path.update(0, value.path[0] - 1), ..value })
        } else {
            before.push(value)
        }
    }
}

/// Removing and reindexing children preserves the container's root descriptor.
pub proof fn remove_root(memory: Seq<Record>, index: int)
    ensures
        lookup(remove_index(memory, index), Seq::empty()) == lookup(memory, Seq::empty()),
    decreases memory.len(),
{
    reveal_with_fuel(remove_index, 2);
    reveal_with_fuel(lookup, 2);
    if memory.len() > 0 {
        remove_root(memory.drop_last(), index);
        let before = remove_index(memory.drop_last(), index);
        let value = memory.last();
        assert(memory =~= memory.drop_last().push(value));
        if value.path.len() == 0 || value.path[0] != index {
            let next = if value.path.len() > 0 && value.path[0] > index {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else {
                value
            };
            assert(next.path.len() == value.path.len());
            if value.path.len() == 0 {
                assert(value.path =~= Seq::<int>::empty());
            }
            lookup_push(before, next, Seq::empty());
        }
    }
}

/// Reindexing changes paths alone; removal transfers precisely one footprint.
pub proof fn remove_partition(memory: Seq<Record>, index: int)
    requires
        well_formed(memory),
    ensures
        well_formed(remove_index(memory, index)),
        cost(memory, 0) == cost(subtree(memory, seq![index]), 0) + cost(
            remove_index(memory, index),
            0,
        ),
        cost(subtree(memory, seq![index]), 0) >= 0,
        cost(remove_index(memory, index), 0) >= 0,
    decreases memory.len(),
{
    reveal_with_fuel(remove_index, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        remove_partition(memory.drop_last(), index);
        let value = memory.last();
        let before = remove_index(memory.drop_last(), index);
        if value.path.len() > 0 && value.path[0] == index {
            assert(seq![index] =~= value.path.take(1));
        } else if value.path.len() > 0 {
            assert(seq![index][0] != value.path.take(1)[0]);
        }
        assert(seq![index].is_prefix_of(value.path) == (value.path.len() > 0 && value.path[0]
            == index));
        if value.path.len() > 0 && value.path[0] == index {
            cost_push(
                subtree(memory.drop_last(), seq![index]),
                Record { path: value.path.skip(1), ..value },
                0,
            );
        } else {
            let next = if value.path.len() > 0 && value.path[0] > index {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else {
                value
            };
            assert(before.push(next).drop_last() =~= before);
            cost_push(before, next, 0);
        }
    }
    inspect(memory, seq![index]);
    inspect(subtree(memory, seq![index]), Seq::empty());
    inspect(remove_index(memory, index), Seq::empty());
}

/// Removing an index commutes with joining allocation forests.
pub broadcast proof fn remove_add(left: Seq<Record>, right: Seq<Record>, index: int)
    ensures
        #[trigger] remove_index(left + right, index) == remove_index(left, index) + remove_index(
            right,
            index,
        ),
    decreases right.len(),
{
    reveal_with_fuel(remove_index, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        remove_add(left, right.drop_last(), index);
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert(remove_index(left + right, index) =~= remove_index(left, index) + remove_index(
            right,
            index,
        ));
    }
}

/// Runtime siblings move together with all their fixed and repeated children.
pub broadcast proof fn remove_prefix(memory: Seq<Record>, slot: int, index: int)
    ensures
        #[trigger] remove_index(prefix(memory, seq![slot]), index) == if slot == index {
            Seq::<Record>::empty()
        } else {
            prefix(
                memory,
                seq![
                    if slot > index {
                        slot - 1
                    } else {
                        slot
                    },
                ],
            )
        },
    decreases memory.len(),
{
    reveal_with_fuel(remove_index, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        remove_prefix(memory.drop_last(), slot, index);
        let before = prefix(memory.drop_last(), seq![slot]);
        let value = Record { path: seq![slot] + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
        if slot > index {
            assert(value.path.update(0, slot - 1) =~= seq![slot - 1] + memory.last().path);
        }
    }
}

/// Publish indexed views for one checked removal, keeping inverse reindexing
/// local to that forest rather than enabling it for every matching expression.
pub proof fn remove_index_views(memory: Seq<Record>, removed: int)
    ensures
        forall|selected: int|
            selected >= 0 ==> #[trigger] subtree(remove_index(memory, removed), seq![selected])
                == subtree(
                memory,
                seq![
                    if selected < removed {
                        selected
                    } else {
                        selected + 1
                    },
                ],
            ),
{
    assert forall|selected: int| selected >= 0 implies #[trigger] subtree(
        remove_index(memory, removed),
        seq![selected],
    ) == subtree(
        memory,
        seq![
            if selected < removed {
                selected
            } else {
                selected + 1
            },
        ],
    ) by {
        select_remove(memory, removed, selected);
    }
}

/// Expose an inverse index only when a caller requests that surviving child.
/// A removal that leaves its source unchanged needs no additional source
/// request, preventing empty forests from spawning unbounded index requests.
pub proof fn remove_index_requested_views(memory: Seq<Record>, removed: int)
    ensures
        forall|selected: int|
            #![trigger view_requested(remove_index(memory, removed), selected), subtree(remove_index(memory, removed), seq![selected])]
            selected >= 0 && view_requested(remove_index(memory, removed), selected) ==> (subtree(
                remove_index(memory, removed),
                seq![selected],
            ) == subtree(
                memory,
                seq![
                    if selected < removed {
                        selected
                    } else {
                        selected + 1
                    },
                ],
            ) && (memory != remove_index(memory, removed) ==> view_requested(
                memory,
                if selected < removed {
                    selected
                } else {
                    selected + 1
                },
            ))),
{
    assert forall|selected: int|
        #![trigger view_requested(remove_index(memory, removed), selected), subtree(remove_index(memory, removed), seq![selected])]
        selected >= 0 && view_requested(remove_index(memory, removed), selected) implies (subtree(
        remove_index(memory, removed),
        seq![selected],
    ) == subtree(
        memory,
        seq![
            if selected < removed {
                selected
            } else {
                selected + 1
            },
        ],
    ) && (memory != remove_index(memory, removed) ==> view_requested(
        memory,
        if selected < removed {
            selected
        } else {
            selected + 1
        },
    ))) by {
        select_remove(memory, removed, selected);
        reveal(view_requested);
    }
}

/// Removing a runtime index preserves the descriptor classes of survivors.
pub broadcast proof fn partition_remove(memory: Seq<Record>, index: int)
    requires
        index >= 0,
    ensures
        #[trigger] runtime(remove_index(memory, index)) == remove_index(runtime(memory), index),
        nonruntime(remove_index(memory, index)) == nonruntime(memory),
        descendants(remove_index(memory, index)) == remove_index(descendants(memory), index),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(remove_index, 2);
    if memory.len() > 0 {
        partition_remove(memory.drop_last(), index);
        let value = memory.last();
        let before = remove_index(memory.drop_last(), index);
        assert(runtime(memory.drop_last()).push(value).drop_last() =~= runtime(memory.drop_last()));
        assert(nonruntime(memory.drop_last()).push(value).drop_last() =~= nonruntime(
            memory.drop_last(),
        ));
        assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(
            memory.drop_last(),
        ));
        if value.path.len() == 0 || value.path[0] != index {
            let next = if value.path.len() > 0 && value.path[0] > index {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else {
                value
            };
            assert(before.push(next).drop_last() =~= before);
            assert(next.path.len() == value.path.len());
            assert((next.path.len() > 0 && next.path[0] >= 0) == (value.path.len() > 0
                && value.path[0] >= 0));
        }
    }
}

} // verus!
