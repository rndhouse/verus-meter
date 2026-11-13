//! Fixed-path selection, replacement, lookup, and ownership partition proofs.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::cost::{cost, cost_push, cost_runtime_partition};
#[cfg(verus_keep_ghost)]
use super::forest::{
    Record, contains, descendants, empty_record, lookup, nonruntime, prefix, runtime, subtree,
    well_formed, without,
};
#[cfg(verus_keep_ghost)]
use super::removal::remove_index;

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Empty forests have no physical descriptor at any path.
pub broadcast proof fn lookup_empty(path: Seq<int>)
    ensures
        #[trigger] lookup(Seq::<Record>::empty(), path) == empty_record(path),
{
    reveal(lookup);
}

/// Selecting or cutting an empty forest leaves it empty.
pub broadcast proof fn select_empty(path: Seq<int>)
    ensures
        #[trigger] subtree(Seq::empty(), path) == Seq::<Record>::empty(),
        without(Seq::empty(), path) == Seq::<Record>::empty(),
{
    reveal(subtree);
    reveal(without);
}

/// A single runtime or fixed slot overlaps precisely the same slot.
pub broadcast proof fn singleton_prefix(left: int, right: int)
    ensures
        #[trigger] seq![left].is_prefix_of(seq![right]) == (left == right),
{
    if left == right {
        assert(seq![left] =~= seq![right].take(1));
    } else {
        assert(seq![left][0] != seq![right].take(1)[0]);
    }
}

/// A child slot matches the first component of an arbitrary ownership path.
pub broadcast proof fn slot_prefix(index: int, path: Seq<int>)
    ensures
        #[trigger] seq![index].is_prefix_of(path) == (path.len() > 0 && path[0] == index),
{
    if path.len() > 0 && path[0] == index {
        assert(seq![index] =~= path.take(1));
    } else if path.len() > 0 {
        assert(seq![index][0] != path.take(1)[0]);
    }
}

/// Removing a known ownership prefix recovers the relative child path.
pub broadcast proof fn skip_prefix(parent: Seq<int>, child: Seq<int>)
    ensures
        #[trigger] (parent + child).skip(parent.len() as int) == child,
{
    assert((parent + child).skip(parent.len() as int) =~= child);
}

/// Subtree selection and cutting distribute over forest composition.
pub broadcast proof fn select_add(left: Seq<Record>, right: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] subtree(left + right, path) == subtree(left, path) + subtree(right, path),
        without(left + right, path) == without(left, path) + without(right, path),
    decreases right.len(),
{
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        select_add(left, right.drop_last(), path);
        assert((left + right).drop_last() =~= left + right.drop_last());
        if path.is_prefix_of(right.last().path) {
            assert(subtree(left + right, path) =~= subtree(left, path) + subtree(right, path));
        } else {
            assert(without(left + right, path) =~= without(left, path) + without(right, path));
        }
    }
}

/// Selecting a prefixed forest recovers it or a disjoint empty selection.
pub broadcast proof fn select_prefix(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        parent == path ==> #[trigger] subtree(prefix(memory, parent), path) == memory,
        parent == path ==> without(prefix(memory, parent), path) == Seq::<Record>::empty(),
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent) ==> subtree(
            prefix(memory, parent),
            path,
        ) == Seq::<Record>::empty() && without(prefix(memory, parent), path) == prefix(
            memory,
            parent,
        ),
    decreases memory.len(),
{
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        select_prefix(memory.drop_last(), parent, path);
        let before = prefix(memory.drop_last(), parent);
        let value = Record { path: parent + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
        if parent == path {
            assert(value.path.skip(path.len() as int) =~= memory.last().path);
            assert(subtree(prefix(memory, parent), path) =~= memory);
        } else if !parent.is_prefix_of(path) && !path.is_prefix_of(parent) {
            if path.is_prefix_of(value.path) {
                if path.len() <= parent.len() {
                    assert(path.is_prefix_of(parent));
                } else {
                    assert(parent.is_prefix_of(path));
                }
            }
            assert(!path.is_prefix_of(value.path));
        }
    }
}

/// Selection preserves bounds and gives a nonnegative charge for every part.
pub proof fn inspect(memory: Seq<Record>, path: Seq<int>)
    requires
        well_formed(memory),
    ensures
        well_formed(subtree(memory, path)),
        well_formed(without(memory, path)),
        well_formed(runtime(memory)),
        well_formed(nonruntime(memory)),
        lookup(memory, path).bytes >= 0,
        lookup(memory, path).capacity >= 0,
        lookup(memory, path).length >= 0,
        cost(memory, 0) >= 0,
        cost(runtime(memory), 0) >= 0,
        cost(nonruntime(memory), 0) >= 0,
        cost(nonruntime(memory), 0) <= cost(memory, 0),
        lookup(memory, Seq::empty()).kind == 0 ==> lookup(memory, Seq::empty()).bytes <= cost(
            nonruntime(memory),
            0,
        ),
    decreases memory.len(),
{
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        inspect(memory.drop_last(), path);
        let value = memory.last();
        if path.is_prefix_of(value.path) {
            let before = subtree(memory.drop_last(), path);
            let selected = Record { path: value.path.skip(path.len() as int), ..value };
            assert(before.push(selected).drop_last() =~= before);
        } else {
            let before = without(memory.drop_last(), path);
            assert(before.push(value).drop_last() =~= before);
        }
        if value.path.len() > 0 && value.path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
            cost_push(before, value, 0);
        } else {
            let before = nonruntime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
            cost_push(before, value, 0);
        }
    }
    cost_runtime_partition(memory, 0);
}

/// Partitioning a container's own allocation from runtime storage preserves
/// every runtime child's complete footprint and reservation descriptors.
pub broadcast proof fn select_runtime(memory: Seq<Record>, path: Seq<int>)
    requires
        path.len() > 0,
        path[0] >= 0,
    ensures
        #[trigger] subtree(runtime(memory), path) == subtree(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_runtime(memory.drop_last(), path);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
        } else if path.is_prefix_of(value.path) {
            assert(value.path.len() >= path.len());
            assert(path[0] == value.path.take(path.len() as int)[0]);
            assert(path[0] == value.path[0]);
            assert(false);
        }
    }
}

/// Expose one selection step without depending on recursive unfolding fuel.
pub broadcast proof fn select_push(memory: Seq<Record>, value: Record, path: Seq<int>)
    ensures
        #[trigger] subtree(memory.push(value), path) == if path.is_prefix_of(value.path) {
            subtree(memory, path).push(Record { path: value.path.skip(path.len() as int), ..value })
        } else {
            subtree(memory, path)
        },
{
    reveal_with_fuel(subtree, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Descriptor presence composes independently of the forest's sequence order.
pub broadcast proof fn contains_add(left: Seq<Record>, right: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] contains(left + right, path) == (contains(left, path) || contains(right, path)),
    decreases right.len(),
{
    reveal_with_fuel(contains, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        contains_add(left, right.drop_last(), path);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Cutting a child removes precisely the descriptors below that path.
pub broadcast proof fn contains_without(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        #[trigger] contains(without(memory, parent), path) == (contains(memory, path)
            && !parent.is_prefix_of(path)),
    decreases memory.len(),
{
    reveal_with_fuel(contains, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        contains_without(memory.drop_last(), parent, path);
        if !parent.is_prefix_of(memory.last().path) {
            let before = without(memory.drop_last(), parent);
            assert(before.push(memory.last()).drop_last() =~= before);
        }
    }
}

/// Prefixed children cannot acquire descriptors belonging to their parent.
pub broadcast proof fn contains_prefix(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        #[trigger] contains(prefix(memory, parent), path) == (parent.is_prefix_of(path) && contains(
            memory,
            path.skip(parent.len() as int),
        )),
    decreases memory.len(),
{
    reveal_with_fuel(contains, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        contains_prefix(memory.drop_last(), parent, path);
        let before = prefix(memory.drop_last(), parent);
        let value = Record { path: parent + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
        if value.path == path {
            assert(parent.is_prefix_of(path));
            assert(path.skip(parent.len() as int) =~= memory.last().path);
        } else if parent.is_prefix_of(path) {
            assert(parent + path.skip(parent.len() as int) =~= path);
        }
    }
}

/// Runtime forests contain no container or fixed-field allocation descriptor.
pub broadcast proof fn contains_runtime(memory: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] contains(runtime(memory), path) == (path.len() > 0 && path[0] >= 0 && contains(
            memory,
            path,
        )),
    decreases memory.len(),
{
    reveal_with_fuel(contains, 2);
    reveal_with_fuel(runtime, 2);
    if memory.len() > 0 {
        contains_runtime(memory.drop_last(), path);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
        }
    }
}

/// Joining forests preserves the most recent matching allocation descriptor.
pub broadcast proof fn lookup_add(left: Seq<Record>, right: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] lookup(left + right, path) == if contains(right, path) {
            lookup(right, path)
        } else {
            lookup(left, path)
        },
    decreases right.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(contains, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        lookup_add(left, right.drop_last(), path);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A newly appended descriptor supersedes an older descriptor at the same path.
pub broadcast proof fn lookup_push(memory: Seq<Record>, value: Record, path: Seq<int>)
    ensures
        #[trigger] lookup(memory.push(value), path) == if value.path == path {
            value
        } else {
            lookup(memory, path)
        },
{
    reveal_with_fuel(lookup, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// A cut preserves every descriptor outside the removed child.
pub broadcast proof fn lookup_without(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        #[trigger] lookup(without(memory, parent), path) == if parent.is_prefix_of(path) {
            empty_record(path)
        } else {
            lookup(memory, path)
        },
    decreases memory.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        lookup_without(memory.drop_last(), parent, path);
        if !parent.is_prefix_of(memory.last().path) {
            lookup_push(without(memory.drop_last(), parent), memory.last(), path);
        }
    }
}

/// A prefixed descriptor is queried relative to its owning child.
pub broadcast proof fn lookup_prefix(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        #[trigger] lookup(prefix(memory, parent), path) == if parent.is_prefix_of(path) {
            Record { path, ..lookup(memory, path.skip(parent.len() as int)) }
        } else {
            empty_record(path)
        },
    decreases memory.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        lookup_prefix(memory.drop_last(), parent, path);
        let value = Record { path: parent + memory.last().path, ..memory.last() };
        lookup_push(prefix(memory.drop_last(), parent), value, path);
        if parent.is_prefix_of(path) {
            assert(parent + path.skip(parent.len() as int) =~= path);
            if value.path == path {
                assert(memory.last().path =~= path.skip(parent.len() as int));
            }
        } else if value.path == path {
            assert(parent.is_prefix_of(value.path));
        }
    }
}

/// Selection changes the queried path, preserving allocation bounds and kind.
pub broadcast proof fn lookup_subtree(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        #[trigger] lookup(subtree(memory, parent), path) == (Record {
            path,
            ..lookup(memory, parent + path)
        }),
    decreases memory.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        lookup_subtree(memory.drop_last(), parent, path);
        let value = memory.last();
        if parent.is_prefix_of(value.path) {
            let selected = Record { path: value.path.skip(parent.len() as int), ..value };
            lookup_push(subtree(memory.drop_last(), parent), selected, path);
            assert(parent + selected.path =~= value.path);
            if value.path == parent + path {
                assert(selected.path =~= path);
            }
        } else if value.path == parent + path {
            assert(parent.is_prefix_of(value.path));
        }
    }
}

/// Container descriptors remain separate from their runtime children's data.
pub broadcast proof fn lookup_runtime(memory: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] lookup(runtime(memory), path) == if path.len() > 0 && path[0] >= 0 {
            lookup(memory, path)
        } else {
            empty_record(path)
        },
    decreases memory.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(runtime, 2);
    if memory.len() > 0 {
        lookup_runtime(memory.drop_last(), path);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] >= 0 {
            lookup_push(runtime(memory.drop_last()), value, path);
        }
    }
}

/// Cutting one runtime child preserves every disjoint child's descriptors.
pub broadcast proof fn select_without(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures
        parent == path ==> #[trigger] subtree(without(memory, parent), path) == Seq::<
            Record,
        >::empty(),
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent) ==> subtree(
            without(memory, parent),
            path,
        ) == subtree(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(without, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_without(memory.drop_last(), parent, path);
        let value = memory.last();
        if parent.is_prefix_of(value.path) {
            if !parent.is_prefix_of(path) && !path.is_prefix_of(parent) && path.is_prefix_of(
                value.path,
            ) {
                if parent.len() <= path.len() {
                    assert(parent.is_prefix_of(path));
                } else {
                    assert(path.is_prefix_of(parent));
                }
            }
        } else {
            let before = without(memory.drop_last(), parent);
            assert(before.push(value).drop_last() =~= before);
        }
    }
}

/// One operation replaces a child; subsequent selections observe that child or
/// the original disjoint sibling, independently of descriptor ordering.
pub broadcast proof fn select_replacement(
    memory: Seq<Record>,
    child: Seq<Record>,
    parent: Seq<int>,
    path: Seq<int>,
)
    ensures
        parent == path ==> #[trigger] subtree(without(memory, parent) + prefix(child, parent), path)
            == child,
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent) ==> subtree(
            without(memory, parent) + prefix(child, parent),
            path,
        ) == subtree(memory, path),
{
    select_add(without(memory, parent), prefix(child, parent), path);
    select_without(memory, parent, path);
    select_prefix(child, parent, path);
    if parent == path {
        assert(Seq::<Record>::empty() + child =~= child);
    } else if !parent.is_prefix_of(path) && !path.is_prefix_of(parent) {
        assert(subtree(memory, path) + Seq::<Record>::empty() =~= subtree(memory, path));
    }
}

/// The checked frame rule for one runtime-element loan.
pub proof fn runtime_frame(memory: Seq<Record>, child: Seq<Record>, parent: Seq<int>, index: int)
    requires
        parent.len() == 1,
    ensures
        subtree(without(memory, parent) + prefix(child, parent), seq![index]) == if parent == seq![
            index,
        ] {
            child
        } else {
            subtree(memory, seq![index])
        },
{
    assert(parent =~= seq![parent[0]]);
    singleton_prefix(parent[0], index);
    singleton_prefix(index, parent[0]);
    select_replacement(memory, child, parent, seq![index]);
}

/// Replacing a runtime child cannot introduce or remove the parent's descriptor.
pub proof fn runtime_presence(memory: Seq<Record>, child: Seq<Record>, parent: Seq<int>)
    requires
        parent.len() == 1,
    ensures
        contains(without(memory, parent) + prefix(child, parent), Seq::empty()) == contains(
            memory,
            Seq::empty(),
        ),
{
    contains_without(memory, parent, Seq::empty());
    contains_prefix(child, parent, Seq::empty());
    contains_add(without(memory, parent), prefix(child, parent), Seq::empty());
}

/// A surviving runtime index selects its original child after closing the gap.
/// Descendant paths and allocation extents are unchanged by reindexing.
pub broadcast proof fn select_remove(memory: Seq<Record>, removed: int, selected: int)
    ensures
        #[trigger] subtree(remove_index(memory, removed), seq![selected]) == subtree(
            memory,
            seq![
                if selected < removed {
                    selected
                } else {
                    selected + 1
                },
            ],
        ),
    decreases memory.len(),
{
    reveal_with_fuel(remove_index, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_remove(memory.drop_last(), removed, selected);
        let value = memory.last();
        let source = if selected < removed {
            selected
        } else {
            selected + 1
        };
        slot_prefix(source, value.path);
        select_push(memory.drop_last(), value, seq![source]);
        let before = remove_index(memory.drop_last(), removed);
        if value.path.len() > 0 && value.path[0] == removed {
            assert(source != removed);
        } else {
            let next = if value.path.len() > 0 && value.path[0] > removed {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else {
                value
            };
            slot_prefix(selected, next.path);
            assert((next.path.len() > 0 && next.path[0] == selected) == (value.path.len() > 0
                && value.path[0] == source));
            assert(next.path.skip(1) =~= value.path.skip(1));
            select_push(before, next, seq![selected]);
            assert(before.push(next).drop_last() =~= before);
        }
        assert(memory =~= memory.drop_last().push(value));
    }
}

/// Cutting a subtree commutes with each independent descriptor class.
pub broadcast proof fn partition_without(memory: Seq<Record>, path: Seq<int>)
    ensures
        #[trigger] runtime(without(memory, path)) == without(runtime(memory), path),
        nonruntime(without(memory, path)) == without(nonruntime(memory), path),
        descendants(without(memory, path)) == without(descendants(memory), path),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        partition_without(memory.drop_last(), path);
        let before = without(memory.drop_last(), path);
        let value = memory.last();
        assert(runtime(memory.drop_last()).push(value).drop_last() =~= runtime(memory.drop_last()));
        assert(nonruntime(memory.drop_last()).push(value).drop_last() =~= nonruntime(
            memory.drop_last(),
        ));
        assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(
            memory.drop_last(),
        ));
        if !path.is_prefix_of(memory.last().path) {
            assert(before.push(memory.last()).drop_last() =~= before);
        }
    }
}

/// Updating a root descriptor leaves every nonempty ownership view unchanged.
pub broadcast proof fn select_root(memory: Seq<Record>, root: Record, path: Seq<int>)
    requires
        root.path == Seq::<int>::empty(),
        path.len() > 0,
    ensures
        #[trigger] subtree(memory.push(root), path) == subtree(memory, path),
{
    select_push(memory, root, path);
}

/// Descendant selection distributes over finite forest composition.
pub broadcast proof fn descendants_add(left: Seq<Record>, right: Seq<Record>)
    ensures
        #[trigger] descendants(left + right) == descendants(left) + descendants(right),
    decreases right.len(),
{
    reveal_with_fuel(descendants, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        descendants_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Expose one descriptor's membership in the descendant forest.
pub broadcast proof fn descendants_push(memory: Seq<Record>, value: Record)
    ensures
        #[trigger] descendants(memory.push(value)) == if value.path.len() == 0 {
            descendants(memory)
        } else {
            descendants(memory).push(value)
        },
{
    reveal_with_fuel(descendants, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Every allocation below a nonempty prefix is a descendant.
pub broadcast proof fn descendants_prefix(memory: Seq<Record>, path: Seq<int>)
    requires
        path.len() > 0,
    ensures
        #[trigger] descendants(prefix(memory, path)) == prefix(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        descendants_prefix(memory.drop_last(), path);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Removing a root preserves all child ownership views.
pub broadcast proof fn select_descendants(memory: Seq<Record>, path: Seq<int>)
    requires
        path.len() > 0,
    ensures
        #[trigger] subtree(descendants(memory), path) == subtree(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_descendants(memory.drop_last(), path);
        let value = memory.last();
        if value.path.len() > 0 {
            assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(
                memory.drop_last(),
            ));
        }
    }
}

} // verus!
