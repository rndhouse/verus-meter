//! Allocation records, fixed ownership paths, and descriptor validity.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::cost::{cost, cost_partition, cost_push};
#[cfg(verus_keep_ghost)]
use super::selection::{inspect, lookup_push};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// One allocation's charged byte upper bound and reserved-slot lower bound.
pub struct Record {
    /// Position relative to the containing owner.
    pub path: Seq<int>,
    /// Compiler-assigned memory-kind identity.
    pub kind: int,
    /// Upper bound on model storage charged for this allocation.
    pub bytes: int,
    /// Reserved inline element slots, when the node is a sequence.
    pub capacity: int,
    /// Logical child count, independent of the allocation's reserved storage.
    pub length: int,
}

/// A missing allocation has no storage or reservation.
pub open spec fn empty_record(path: Seq<int>) -> Record {
    Record { path, kind: 0, bytes: 0, capacity: 0, length: 0 }
}

/// Resource metadata uses nonnegative byte bounds and reservation minima.
/// Path uniqueness is unnecessary for conservative charge partitioning.
pub open spec fn well_formed(memory: Seq<Record>) -> bool
    decreases memory.len(),
{
    memory.len() == 0 || (well_formed(memory.drop_last()) && memory.last().bytes >= 0
        && memory.last().capacity >= 0 && memory.last().length >= 0)
}

/// One nonnegative allocation is a valid forest.
pub proof fn well_formed_record(value: Record)
    requires
        value.bytes >= 0,
        value.capacity >= 0,
        value.length >= 0,
    ensures
        well_formed(Seq::empty().push(value)),
        contains(Seq::empty().push(value), value.path),
{
    reveal_with_fuel(well_formed, 2);
    assert(Seq::<Record>::empty().push(value).drop_last() =~= Seq::empty());
}

/// A nonnegative descriptor extends any valid allocation forest.
pub proof fn well_formed_push(memory: Seq<Record>, value: Record)
    requires
        well_formed(memory),
        value.bytes >= 0,
        value.capacity >= 0,
        value.length >= 0,
    ensures
        well_formed(memory.push(value)),
{
    reveal_with_fuel(well_formed, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Nonnegative allocation bounds compose across independent forests.
pub proof fn well_formed_add(left: Seq<Record>, right: Seq<Record>)
    requires
        well_formed(left),
        well_formed(right),
    ensures
        well_formed(left + right),
    decreases right.len(),
{
    reveal_with_fuel(well_formed, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        well_formed_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Moving beneath a parent path preserves allocation bounds.
pub proof fn well_formed_prefix(memory: Seq<Record>, path: Seq<int>)
    requires
        well_formed(memory),
    ensures
        well_formed(prefix(memory, path)),
    decreases memory.len(),
{
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        well_formed_prefix(memory.drop_last(), path);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Select runtime children without including the container's own allocation.
pub open spec fn runtime(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = runtime(memory.drop_last());
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            before.push(memory.last())
        } else {
            before
        }
    }
}

/// The container allocation and fixed children, excluding indexed children.
pub open spec fn nonruntime(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = nonruntime(memory.drop_last());
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            before
        } else {
            before.push(memory.last())
        }
    }
}

/// Find the most recently installed descriptor at an allocation path.
#[verifier::opaque]
pub open spec fn lookup(memory: Seq<Record>, path: Seq<int>) -> Record
    decreases memory.len(),
{
    if memory.len() == 0 {
        empty_record(path)
    } else if memory.last().path == path {
        memory.last()
    } else {
        lookup(memory.drop_last(), path)
    }
}

/// Whether the owner contains the requested allocation node.
pub open spec fn contains(memory: Seq<Record>, path: Seq<int>) -> bool
    decreases memory.len(),
{
    memory.len() > 0 && (memory.last().path == path || contains(memory.drop_last(), path))
}

/// Place an owner's complete footprint under a parent path.
#[verifier::opaque]
pub open spec fn prefix(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        prefix(memory.drop_last(), path).push(
            Record { path: path + memory.last().path, ..memory.last() },
        )
    }
}

/// Select a complete subtree and make its paths relative to its new root.
#[verifier::opaque]
pub open spec fn subtree(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = subtree(memory.drop_last(), path);
        if path.is_prefix_of(memory.last().path) {
            before.push(
                Record { path: memory.last().path.skip(path.len() as int), ..memory.last() },
            )
        } else {
            before
        }
    }
}

/// Keep the enclosing allocation and all siblings when detaching a subtree.
#[verifier::opaque]
pub open spec fn without(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = without(memory.drop_last(), path);
        if path.is_prefix_of(memory.last().path) {
            before
        } else {
            before.push(memory.last())
        }
    }
}

/// Replacement preserves the rest of the owner and installs one complete child.
pub open spec fn replace(memory: Seq<Record>, path: Seq<int>, child: Seq<Record>) -> Seq<Record> {
    without(memory, path) + prefix(child, path)
}

/// Removing an indexed subtree cannot move backing bytes into child charges.
/// Filtering and exclusion commute even for an absent optional child.
pub proof fn runtime_without_facts(memory: Seq<Record>, path: Seq<int>)
    requires
        well_formed(memory),
    ensures
        runtime(without(memory, path)) == without(runtime(memory), path),
        cost(runtime(without(memory, path)), 0) <= cost(runtime(memory), 0),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        runtime_without_facts(memory.drop_last(), path);
        let value = memory.last();
        if !path.is_prefix_of(value.path) {
            let before = without(memory.drop_last(), path);
            assert(before.push(value).drop_last() =~= before);
            runtime_push(before, value);
        }
        if value.path.len() > 0 && value.path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(value).drop_last() =~= before);
        }
    }
    inspect(memory, path);
    inspect(runtime(memory), path);
    inspect(subtree(runtime(memory), path), Seq::empty());
    cost_partition(runtime(memory), path, 0);
}

/// Construct an allocation descriptor without introducing executable storage.
pub open spec fn allocated(
    path: Seq<int>,
    kind: int,
    bytes: int,
    capacity: int,
    length: int,
) -> Record {
    Record { path, kind, bytes, capacity, length }
}

/// All allocations below an owner, excluding its own root descriptor.
pub open spec fn descendants(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 {
        Seq::empty()
    } else {
        let before = descendants(memory.drop_last());
        if memory.last().path.len() == 0 {
            before
        } else {
            before.push(memory.last())
        }
    }
}

/// Update an owner's allocation and geometry while preserving its children.
pub open spec fn with_root(memory: Seq<Record>, root: Record) -> Seq<Record> {
    descendants(memory).push(root)
}

/// Root updates preserve valid child descriptors and expose the new root.
pub proof fn with_root_facts(memory: Seq<Record>, root: Record)
    requires
        well_formed(memory),
        root.path == Seq::<int>::empty(),
        root.bytes >= 0,
        root.capacity >= 0,
        root.length >= 0,
    ensures
        well_formed(with_root(memory, root)),
        lookup(with_root(memory, root), Seq::empty()) == root,
        cost(with_root(memory, root), 0) == cost(descendants(memory), 0) + if root.kind == 0 {
            root.bytes
        } else {
            0
        },
{
    descendants_facts(memory);
    reveal_with_fuel(well_formed, 2);
    assert(descendants(memory).push(root).drop_last() =~= descendants(memory));
    lookup_push(descendants(memory), root, Seq::empty());
    cost_push(descendants(memory), root, 0);
}

/// Removing roots preserves validity. Descendants and the selected root are
/// disjoint charges; any duplicate root descriptors only increase the total.
pub proof fn descendants_facts(memory: Seq<Record>)
    requires
        well_formed(memory),
    ensures
        well_formed(descendants(memory)),
        !contains(descendants(memory), Seq::empty()),
        cost(descendants(memory), 0) >= 0,
        cost(descendants(memory), 0) + (if lookup(memory, Seq::empty()).kind == 0 {
            lookup(memory, Seq::empty()).bytes
        } else {
            0
        }) <= cost(memory, 0),
    decreases memory.len(),
{
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(well_formed, 2);
    reveal_with_fuel(contains, 2);
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(lookup, 2);
    if memory.len() > 0 {
        descendants_facts(memory.drop_last());
        inspect(memory.drop_last(), Seq::empty());
        lookup_push(memory.drop_last(), memory.last(), Seq::empty());
        assert(memory =~= memory.drop_last().push(memory.last()));
        if memory.last().path.len() != 0 {
            assert(descendants(memory.drop_last()).push(memory.last()).drop_last() =~= descendants(
                memory.drop_last(),
            ));
            cost_push(descendants(memory.drop_last()), memory.last(), 0);
        } else {
            assert(memory.last().path =~= Seq::<int>::empty());
        }
    }
}

/// Runtime and fixed partitions distribute over composition.
pub broadcast proof fn runtime_add(left: Seq<Record>, right: Seq<Record>)
    ensures
        #[trigger] runtime(left + right) == runtime(left) + runtime(right),
        nonruntime(left + right) == nonruntime(left) + nonruntime(right),
    decreases right.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        runtime_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A descriptor belongs to exactly one structural partition.
pub broadcast proof fn runtime_push(memory: Seq<Record>, value: Record)
    ensures
        #[trigger] runtime(memory.push(value)) == if value.path.len() > 0 && value.path[0] >= 0 {
            runtime(memory).push(value)
        } else {
            runtime(memory)
        },
        nonruntime(memory.push(value)) == if value.path.len() > 0 && value.path[0] >= 0 {
            nonruntime(memory)
        } else {
            nonruntime(memory).push(value)
        },
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Prefixing an owner places its complete footprint in one structural class.
pub broadcast proof fn runtime_prefix(memory: Seq<Record>, path: Seq<int>)
    requires
        path.len() > 0,
    ensures
        #[trigger] runtime(prefix(memory, path)) == if path[0] >= 0 {
            prefix(memory, path)
        } else {
            Seq::<Record>::empty()
        },
        nonruntime(prefix(memory, path)) == if path[0] >= 0 {
            Seq::<Record>::empty()
        } else {
            prefix(memory, path)
        },
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        runtime_prefix(memory.drop_last(), path);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// An already partitioned runtime forest has no root or fixed descriptors.
pub broadcast proof fn runtime_class(memory: Seq<Record>)
    ensures
        #[trigger] runtime(runtime(memory)) == runtime(memory),
        nonruntime(runtime(memory)) == Seq::<Record>::empty(),
        descendants(runtime(memory)) == runtime(memory),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(descendants, 2);
    if memory.len() > 0 {
        runtime_class(memory.drop_last());
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            let before = runtime(memory.drop_last());
            assert(before.push(memory.last()).drop_last() =~= before);
        }
    }
}

} // verus!
