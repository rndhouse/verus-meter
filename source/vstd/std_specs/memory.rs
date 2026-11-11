//! Erased allocation metadata used by compiler-generated resource proofs.
//!
//! Paths identify allocations within an owner. Nonnegative path components are
//! runtime element indices; negative components identify fixed child positions.
//! Bytes are charged upper bounds; capacities are independently maintained
//! reservation lower bounds. No executable allocation metadata is introduced.

use crate::prelude::*;

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
    memory.len() == 0 || (well_formed(memory.drop_last())
        && memory.last().bytes >= 0 && memory.last().capacity >= 0
        && memory.last().length >= 0)
}

/// One nonnegative allocation is a valid forest.
pub proof fn well_formed_record(value: Record)
    requires value.bytes >= 0, value.capacity >= 0, value.length >= 0,
    ensures well_formed(Seq::empty().push(value)),
        contains(Seq::empty().push(value), value.path),
{
    reveal_with_fuel(well_formed, 2);
    assert(Seq::<Record>::empty().push(value).drop_last() =~= Seq::empty());
}

/// A nonnegative descriptor extends any valid allocation forest.
pub proof fn well_formed_push(memory: Seq<Record>, value: Record)
    requires well_formed(memory), value.bytes >= 0, value.capacity >= 0, value.length >= 0,
    ensures well_formed(memory.push(value)),
{
    reveal_with_fuel(well_formed, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// An empty forest contributes no charge in any memory kind.
pub broadcast proof fn cost_empty(kind: int)
    ensures #[trigger] cost(Seq::empty(), kind) == 0,
{
    reveal(cost);
}

/// Empty forests have no physical descriptor at any path.
pub broadcast proof fn lookup_empty(path: Seq<int>)
    ensures #[trigger] lookup(Seq::<Record>::empty(), path) == empty_record(path),
{ reveal(lookup); }

/// Selecting or cutting an empty forest leaves it empty.
pub broadcast proof fn select_empty(path: Seq<int>)
    ensures #[trigger] subtree(Seq::empty(), path) == Seq::<Record>::empty(),
        without(Seq::empty(), path) == Seq::<Record>::empty(),
{
    reveal(subtree);
    reveal(without);
}

/// A single runtime or fixed slot overlaps precisely the same slot.
pub broadcast proof fn singleton_prefix(left: int, right: int)
    ensures #[trigger] seq![left].is_prefix_of(seq![right]) == (left == right),
{
    if left == right { assert(seq![left] =~= seq![right].take(1)); }
    else { assert(seq![left][0] != seq![right].take(1)[0]); }
}

/// A child slot matches the first component of an arbitrary ownership path.
pub broadcast proof fn slot_prefix(index: int, path: Seq<int>)
    ensures #[trigger] seq![index].is_prefix_of(path)
        == (path.len() > 0 && path[0] == index),
{
    if path.len() > 0 && path[0] == index {
        assert(seq![index] =~= path.take(1));
    } else if path.len() > 0 {
        assert(seq![index][0] != path.take(1)[0]);
    }
}

/// Removing a known ownership prefix recovers the relative child path.
pub broadcast proof fn skip_prefix(parent: Seq<int>, child: Seq<int>)
    ensures #[trigger] (parent + child).skip(parent.len() as int) == child,
{
    assert((parent + child).skip(parent.len() as int) =~= child);
}

/// Subtree selection and cutting distribute over forest composition.
pub broadcast proof fn select_add(left: Seq<Record>, right: Seq<Record>, path: Seq<int>)
    ensures #[trigger] subtree(left + right, path) == subtree(left, path) + subtree(right, path),
        without(left + right, path) == without(left, path) + without(right, path),
    decreases right.len(),
{
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
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
    ensures parent == path ==> #[trigger] subtree(prefix(memory, parent), path) == memory,
        parent == path ==> without(prefix(memory, parent), path) == Seq::<Record>::empty(),
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent)
            ==> subtree(prefix(memory, parent), path) == Seq::<Record>::empty()
                && without(prefix(memory, parent), path) == prefix(memory, parent),
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
                if path.len() <= parent.len() { assert(path.is_prefix_of(parent)); }
                else { assert(parent.is_prefix_of(path)); }
            }
            assert(!path.is_prefix_of(value.path));
        }
    }
}

// Keep lookup_subtree explicit: flattening every composed ownership path can
// multiply matching terms across a sequence of operations.
pub broadcast group group_metadata_algebra {
    Seq::add_empty_left,
    Seq::add_empty_right,
    cost_empty,
    lookup_empty,
    select_empty,
    singleton_prefix,
    skip_prefix,
    select_add,
    select_prefix,
    cost_add,
    cost_push,
    cost_prefix,
    cost_repeat,
    remove_add,
    remove_prefix,
    lookup_add,
    lookup_push,
    lookup_runtime,
    select_without,
    select_replacement,
}

/// Reusable ownership proofs also need views of arbitrary sibling indices.
/// Keep these rules separate from ordinary finite element transfers.
pub broadcast group group_metadata_loop_algebra {
    select_push,
    lookup_without,
    lookup_prefix,
    select_runtime,
    contains_add,
    contains_without,
    contains_prefix,
    contains_runtime,
}

/// Nonnegative allocation bounds compose across independent forests.
pub proof fn well_formed_add(left: Seq<Record>, right: Seq<Record>)
    requires well_formed(left), well_formed(right),
    ensures well_formed(left + right),
    decreases right.len(),
{
    reveal_with_fuel(well_formed, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        well_formed_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Moving beneath a parent path preserves allocation bounds.
pub proof fn well_formed_prefix(memory: Seq<Record>, path: Seq<int>)
    requires well_formed(memory),
    ensures well_formed(prefix(memory, path)),
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

/// Selection preserves bounds and gives a nonnegative charge for every part.
pub proof fn inspect(memory: Seq<Record>, path: Seq<int>)
    requires well_formed(memory),
    ensures well_formed(subtree(memory, path)), well_formed(without(memory, path)),
        well_formed(runtime(memory)), well_formed(nonruntime(memory)),
        lookup(memory, path).bytes >= 0,
        lookup(memory, path).capacity >= 0,
        lookup(memory, path).length >= 0,
        cost(memory, 0) >= 0,
        cost(runtime(memory), 0) >= 0,
        cost(nonruntime(memory), 0) >= 0,
        cost(nonruntime(memory), 0) <= cost(memory, 0),
        lookup(memory, Seq::empty()).kind == 0 ==>
            lookup(memory, Seq::empty()).bytes <= cost(nonruntime(memory), 0),
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




/// Select runtime children without including the container's own allocation.
pub open spec fn runtime(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = runtime(memory.drop_last());
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            before.push(memory.last())
        } else { before }
    }
}

/// The container allocation and fixed children, excluding indexed children.
pub open spec fn nonruntime(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = nonruntime(memory.drop_last());
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            before
        } else { before.push(memory.last()) }
    }
}

/// Partitioning a container's own allocation from runtime storage preserves
/// every runtime child's complete footprint and reservation descriptors.
pub broadcast proof fn select_runtime(memory: Seq<Record>, path: Seq<int>)
    requires path.len() > 0, path[0] >= 0,
    ensures #[trigger] subtree(runtime(memory), path) == subtree(memory, path),
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

/// The two structural classes partition the charge without geometry assumptions.
pub proof fn cost_runtime_partition(memory: Seq<Record>, kind: int)
    ensures cost(memory, kind) == cost(runtime(memory), kind)
        + cost(nonruntime(memory), kind),
        !contains(runtime(memory), Seq::empty()),
        forall|index: int| index >= 0 ==>
            #[trigger] subtree(runtime(memory), seq![index]) == subtree(memory, seq![index]),
    decreases memory.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    reveal_with_fuel(cost, 2);
    if memory.len() > 0 {
        cost_runtime_partition(memory.drop_last(), kind);
        if memory.last().path.len() > 0 && memory.last().path[0] >= 0 {
            cost_push(runtime(memory.drop_last()), memory.last(), kind);
        } else { cost_push(nonruntime(memory.drop_last()), memory.last(), kind); }
    }
    contains_runtime(memory, Seq::empty());
    assert forall|index: int| index >= 0 implies
        #[trigger] subtree(runtime(memory), seq![index]) == subtree(memory, seq![index]) by {
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
    if memory.len() == 0 { 0 } else {
        cost(memory.drop_last(), kind)
            + if memory.last().kind == kind { memory.last().bytes } else { 0 }
    }
}

/// Find the most recently installed descriptor at an allocation path.
#[verifier::opaque]
pub open spec fn lookup(memory: Seq<Record>, path: Seq<int>) -> Record
    decreases memory.len(),
{
    if memory.len() == 0 { empty_record(path) }
    else if memory.last().path == path { memory.last() }
    else { lookup(memory.drop_last(), path) }
}

/// Whether the owner contains the requested allocation node.
pub open spec fn contains(memory: Seq<Record>, path: Seq<int>) -> bool
    decreases memory.len(),
{
    memory.len() > 0 && (memory.last().path == path || contains(memory.drop_last(), path))
}

/// Expose one selection step without depending on recursive unfolding fuel.
pub broadcast proof fn select_push(memory: Seq<Record>, value: Record, path: Seq<int>)
    ensures #[trigger] subtree(memory.push(value), path)
        == if path.is_prefix_of(value.path) {
            subtree(memory, path).push(Record { path: value.path.skip(path.len() as int), ..value })
        } else { subtree(memory, path) },
{
    reveal_with_fuel(subtree, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Descriptor presence composes independently of the forest's sequence order.
pub broadcast proof fn contains_add(left: Seq<Record>, right: Seq<Record>, path: Seq<int>)
    ensures #[trigger] contains(left + right, path) == (contains(left, path) || contains(right, path)),
    decreases right.len(),
{
    reveal_with_fuel(contains, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        contains_add(left, right.drop_last(), path);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Cutting a child removes precisely the descriptors below that path.
pub broadcast proof fn contains_without(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures #[trigger] contains(without(memory, parent), path)
        == (contains(memory, path) && !parent.is_prefix_of(path)),
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
    ensures #[trigger] contains(prefix(memory, parent), path)
        == (parent.is_prefix_of(path) && contains(memory, path.skip(parent.len() as int))),
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
    ensures #[trigger] contains(runtime(memory), path)
        == (path.len() > 0 && path[0] >= 0 && contains(memory, path)),
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
    ensures #[trigger] lookup(left + right, path)
        == if contains(right, path) { lookup(right, path) } else { lookup(left, path) },
    decreases right.len(),
{
    reveal_with_fuel(lookup, 2);
    reveal_with_fuel(contains, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        lookup_add(left, right.drop_last(), path);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A newly appended descriptor supersedes an older descriptor at the same path.
pub broadcast proof fn lookup_push(memory: Seq<Record>, value: Record, path: Seq<int>)
    ensures #[trigger] lookup(memory.push(value), path)
        == if value.path == path { value } else { lookup(memory, path) },
{
    reveal_with_fuel(lookup, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// A cut preserves every descriptor outside the removed child.
pub broadcast proof fn lookup_without(memory: Seq<Record>, parent: Seq<int>, path: Seq<int>)
    ensures #[trigger] lookup(without(memory, parent), path)
        == if parent.is_prefix_of(path) { empty_record(path) } else { lookup(memory, path) },
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
    ensures #[trigger] lookup(prefix(memory, parent), path)
        == if parent.is_prefix_of(path) {
            Record { path, ..lookup(memory, path.skip(parent.len() as int)) }
        } else { empty_record(path) },
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
    ensures #[trigger] lookup(subtree(memory, parent), path)
        == (Record { path, ..lookup(memory, parent + path) }),
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
            if value.path == parent + path { assert(selected.path =~= path); }
        } else if value.path == parent + path {
            assert(parent.is_prefix_of(value.path));
        }
    }
}

/// Container descriptors remain separate from their runtime children's data.
pub broadcast proof fn lookup_runtime(memory: Seq<Record>, path: Seq<int>)
    ensures #[trigger] lookup(runtime(memory), path)
        == if path.len() > 0 && path[0] >= 0 { lookup(memory, path) } else { empty_record(path) },
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
    ensures parent == path ==> #[trigger] subtree(without(memory, parent), path) == Seq::<Record>::empty(),
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent)
            ==> subtree(without(memory, parent), path) == subtree(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(without, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_without(memory.drop_last(), parent, path);
        let value = memory.last();
        if parent.is_prefix_of(value.path) {
            if !parent.is_prefix_of(path) && !path.is_prefix_of(parent) && path.is_prefix_of(value.path) {
                if parent.len() <= path.len() { assert(parent.is_prefix_of(path)); }
                else { assert(path.is_prefix_of(parent)); }
            }
        } else {
            let before = without(memory.drop_last(), parent);
            assert(before.push(value).drop_last() =~= before);
        }
    }
}

/// One operation replaces a child; subsequent selections observe that child or
/// the original disjoint sibling, independently of descriptor ordering.
pub broadcast proof fn select_replacement(memory: Seq<Record>, child: Seq<Record>,
    parent: Seq<int>, path: Seq<int>)
    ensures parent == path ==>
        #[trigger] subtree(without(memory, parent) + prefix(child, parent), path) == child,
        !parent.is_prefix_of(path) && !path.is_prefix_of(parent) ==>
            subtree(without(memory, parent) + prefix(child, parent), path) == subtree(memory, path),
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
    requires parent.len() == 1,
    ensures subtree(without(memory, parent) + prefix(child, parent), seq![index])
        == if parent == seq![index] { child } else { subtree(memory, seq![index]) },
{
    assert(parent =~= seq![parent[0]]);
    singleton_prefix(parent[0], index);
    singleton_prefix(index, parent[0]);
    select_replacement(memory, child, parent, seq![index]);
}

/// Replacing a runtime child cannot introduce or remove the parent's descriptor.
pub proof fn runtime_presence(memory: Seq<Record>, child: Seq<Record>, parent: Seq<int>)
    requires parent.len() == 1,
    ensures contains(without(memory, parent) + prefix(child, parent), Seq::empty())
        == contains(memory, Seq::empty()),
{
    contains_without(memory, parent, Seq::empty());
    contains_prefix(child, parent, Seq::empty());
    contains_add(without(memory, parent), prefix(child, parent), Seq::empty());
}

/// Place an owner's complete footprint under a parent path.
#[verifier::opaque]
pub open spec fn prefix(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        prefix(memory.drop_last(), path).push(Record {
            path: path + memory.last().path, ..memory.last()
        })
    }
}

/// Select a complete subtree and make its paths relative to its new root.
#[verifier::opaque]
pub open spec fn subtree(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = subtree(memory.drop_last(), path);
        if path.is_prefix_of(memory.last().path) {
            before.push(Record { path: memory.last().path.skip(path.len() as int), ..memory.last() })
        } else { before }
    }
}

/// Keep the enclosing allocation and all siblings when detaching a subtree.
#[verifier::opaque]
pub open spec fn without(memory: Seq<Record>, path: Seq<int>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = without(memory.drop_last(), path);
        if path.is_prefix_of(memory.last().path) { before } else { before.push(memory.last()) }
    }
}

/// Replacement preserves the rest of the owner and installs one complete child.
pub open spec fn replace(memory: Seq<Record>, path: Seq<int>, child: Seq<Record>) -> Seq<Record> {
    without(memory, path) + prefix(child, path)
}

/// Remove one runtime child and shift the surviving indices with the container.
pub open spec fn remove_index(memory: Seq<Record>, index: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = remove_index(memory.drop_last(), index);
        let value = memory.last();
        if value.path.len() > 0 && value.path[0] == index { before }
        else if value.path.len() > 0 && value.path[0] > index {
            before.push(Record { path: value.path.update(0, value.path[0] - 1), ..value })
        } else { before.push(value) }
    }
}

/// Removing and reindexing children preserves the container's root descriptor.
pub proof fn remove_root(memory: Seq<Record>, index: int)
    ensures lookup(remove_index(memory, index), Seq::empty()) == lookup(memory, Seq::empty()),
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
            } else { value };
            assert(next.path.len() == value.path.len());
            if value.path.len() == 0 { assert(value.path =~= Seq::<int>::empty()); }
            lookup_push(before, next, Seq::empty());
        }
    }
}

/// Reindexing changes paths alone; removal transfers precisely one footprint.
pub proof fn remove_partition(memory: Seq<Record>, index: int)
    requires well_formed(memory),
    ensures well_formed(remove_index(memory, index)),
        cost(memory, 0) == cost(subtree(memory, seq![index]), 0)
            + cost(remove_index(memory, index), 0),
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
        assert(seq![index].is_prefix_of(value.path) == (value.path.len() > 0 && value.path[0] == index));
        if value.path.len() > 0 && value.path[0] == index {
            cost_push(subtree(memory.drop_last(), seq![index]), Record { path: value.path.skip(1), ..value }, 0);
        } else {
            let next = if value.path.len() > 0 && value.path[0] > index {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else { value };
            assert(before.push(next).drop_last() =~= before);
            cost_push(before, next, 0);
        }
    }
}

/// Removing an index commutes with joining allocation forests.
pub broadcast proof fn remove_add(left: Seq<Record>, right: Seq<Record>, index: int)
    ensures #[trigger] remove_index(left + right, index)
        == remove_index(left, index) + remove_index(right, index),
    decreases right.len(),
{
    reveal_with_fuel(remove_index, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        remove_add(left, right.drop_last(), index);
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert(remove_index(left + right, index) =~= remove_index(left, index) + remove_index(right, index));
    }
}

/// Runtime siblings move together with all their fixed and repeated children.
pub broadcast proof fn remove_prefix(memory: Seq<Record>, slot: int, index: int)
    ensures #[trigger] remove_index(prefix(memory, seq![slot]), index)
        == if slot == index { Seq::<Record>::empty() }
            else { prefix(memory, seq![if slot > index { slot - 1 } else { slot }]) },
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

/// Repeated children keep their full nested forest at consecutive indices.
/// Callers use `repeat_facts` to avoid recursively expanding a whole region.
#[verifier::opaque]
pub open spec fn repeat(child: Seq<Record>, start: int, count: int) -> Seq<Record>
    decreases count,
{
    if count <= 0 { Seq::empty() } else {
        repeat(child, start, count - 1) + prefix(child, seq![start + count - 1])
    }
}

/// Quantitative views of a repeated region stay available after range cuts.
pub broadcast proof fn cost_repeat(child: Seq<Record>, start: int, count: int, kind: int)
    requires count >= 0,
    ensures #[trigger] cost(repeat(child, start, count), kind) == count * cost(child, kind),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    if count > 0 {
        cost_repeat(child, start, count - 1, kind);
        let before = repeat(child, start, count - 1);
        let path = seq![start + count - 1];
        cost_prefix(child, path, kind);
        cost_add(before, prefix(child, path), kind);
        assert(cost(repeat(child, start, count), kind)
            == cost(before, kind) + cost(child, kind));
        assert((count - 1) * cost(child, kind) + cost(child, kind)
            == count * cost(child, kind)) by (nonlinear_arith);
        assert(cost(repeat(child, start, count), kind) == count * cost(child, kind));
    } else {
        cost_empty(kind);
        assert(count * cost(child, kind) == 0) by (nonlinear_arith)
            requires count == 0;
    }
}

/// A repeated region has a uniform per-element footprint and exact index views.
pub proof fn repeat_facts(child: Seq<Record>, start: int, count: int)
    requires well_formed(child), start >= 0, count >= 0,
    ensures well_formed(repeat(child, start, count)),
        cost(repeat(child, start, count), 0) == count * cost(child, 0),
        runtime(repeat(child, start, count)) == repeat(child, start, count),
        nonruntime(repeat(child, start, count)) == Seq::<Record>::empty(),
        descendants(repeat(child, start, count)) == repeat(child, start, count),
        forall|index: int| #[trigger] subtree(repeat(child, start, count), seq![index]) ==
            if start <= index < start + count { child } else { Seq::<Record>::empty() },
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
    assert forall|index: int| #[trigger] subtree(repeat(child, start, count), seq![index]) ==
        if start <= index < start + count { child } else { Seq::<Record>::empty() } by {
        if count > 0 {
            let before = repeat(child, start, count - 1);
            let path = seq![start + count - 1];
            select_add(before, prefix(child, path), seq![index]);
            select_prefix(child, path, seq![index]);
            singleton_prefix(start + count - 1, index);
            singleton_prefix(index, start + count - 1);
        } else { select_empty(seq![index]); }
    }
}

/// Keep the existing runtime children before a logical end index.
pub open spec fn take_children(memory: Seq<Record>, length: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = take_children(memory.drop_last(), length);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] < length { before.push(value) } else { before }
    }
}

/// Retaining a range never increases storage and preserves its child views.
pub proof fn take_children_facts(memory: Seq<Record>, length: int)
    requires well_formed(memory),
    ensures well_formed(take_children(memory, length)),
        0 <= cost(take_children(memory, length), 0) <= cost(memory, 0),
        runtime(take_children(memory, length)) == take_children(memory, length),
        nonruntime(take_children(memory, length)) == Seq::<Record>::empty(),
        descendants(take_children(memory, length)) == take_children(memory, length),
        forall|index: int| #[trigger] subtree(take_children(memory, length), seq![index]) ==
            if 0 <= index < length { subtree(memory, seq![index]) } else { Seq::<Record>::empty() },
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
        assert forall|index: int| #[trigger] subtree(take_children(memory, length), seq![index]) ==
            if 0 <= index < length { subtree(memory, seq![index]) } else { Seq::<Record>::empty() } by {
            select_push(memory.drop_last(), value, seq![index]);
            if value.path.len() > 0 && 0 <= value.path[0] < length {
                select_push(before, value, seq![index]);
            }
            slot_prefix(index, value.path);
        }
    }
}

/// Range retention distributes over independently composed allocation forests.
pub broadcast proof fn take_children_add(left: Seq<Record>, right: Seq<Record>, length: int)
    ensures #[trigger] take_children(left + right, length) == take_children(left, length) + take_children(right, length),
    decreases right.len(),
{
    reveal_with_fuel(take_children, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        take_children_add(left, right.drop_last(), length);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A complete child is retained or released according to its runtime index.
pub broadcast proof fn take_children_prefix(memory: Seq<Record>, path: Seq<int>, length: int)
    requires path.len() > 0,
    ensures #[trigger] take_children(prefix(memory, path), length) ==
        if 0 <= path[0] < length { prefix(memory, path) } else { Seq::<Record>::empty() },
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
    requires start >= 0, count >= 0,
    ensures #[trigger] take_children(repeat(child, start, count), length) ==
        repeat(child, start, if length <= start { 0 } else if length >= start + count { count } else { length - start }),
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

/// Construct an allocation descriptor without introducing executable storage.
pub open spec fn allocated(path: Seq<int>, kind: int, bytes: int, capacity: int, length: int) -> Record {
    Record { path, kind, bytes, capacity, length }
}

/// All allocations below an owner, excluding its own root descriptor.
pub open spec fn descendants(memory: Seq<Record>) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = descendants(memory.drop_last());
        if memory.last().path.len() == 0 { before } else { before.push(memory.last()) }
    }
}

/// Update an owner's allocation and geometry while preserving its children.
pub open spec fn with_root(memory: Seq<Record>, root: Record) -> Seq<Record> {
    descendants(memory).push(root)
}

/// Root updates preserve valid child descriptors and expose the new root.
pub proof fn with_root_facts(memory: Seq<Record>, root: Record)
    requires well_formed(memory), root.path == Seq::<int>::empty(),
        root.bytes >= 0, root.capacity >= 0, root.length >= 0,
    ensures well_formed(with_root(memory, root)),
        lookup(with_root(memory, root), Seq::empty()) == root,
        cost(with_root(memory, root), 0) == cost(descendants(memory), 0)
            + if root.kind == 0 { root.bytes } else { 0 },
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
    requires well_formed(memory),
    ensures well_formed(descendants(memory)),
        !contains(descendants(memory), Seq::empty()),
        cost(descendants(memory), 0) >= 0,
        cost(descendants(memory), 0)
            + (if lookup(memory, Seq::empty()).kind == 0 { lookup(memory, Seq::empty()).bytes } else { 0 })
            <= cost(memory, 0),
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
            assert(descendants(memory.drop_last()).push(memory.last()).drop_last() =~= descendants(memory.drop_last()));
            cost_push(descendants(memory.drop_last()), memory.last(), 0);
        } else {
            assert(memory.last().path =~= Seq::<int>::empty());
        }
    }
}

/// Descriptor-class rewrites for local shape proofs. Keep these scoped to
/// shape assertions rather than activating them throughout budget queries.
pub broadcast group group_runtime_shape {
    runtime_add,
    runtime_push,
    runtime_prefix,
    runtime_class,
    partition_without,
    partition_remove,
}

/// Cutting a subtree commutes with each independent descriptor class.
pub broadcast proof fn partition_without(memory: Seq<Record>, path: Seq<int>)
    ensures #[trigger] runtime(without(memory, path)) == without(runtime(memory), path),
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
        assert(nonruntime(memory.drop_last()).push(value).drop_last() =~= nonruntime(memory.drop_last()));
        assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(memory.drop_last()));
        if !path.is_prefix_of(memory.last().path) {
            assert(before.push(memory.last()).drop_last() =~= before);
        }
    }
}

/// Removing a runtime index preserves the descriptor classes of survivors.
pub broadcast proof fn partition_remove(memory: Seq<Record>, index: int)
    requires index >= 0,
    ensures #[trigger] runtime(remove_index(memory, index)) == remove_index(runtime(memory), index),
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
        assert(nonruntime(memory.drop_last()).push(value).drop_last() =~= nonruntime(memory.drop_last()));
        assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(memory.drop_last()));
        if value.path.len() == 0 || value.path[0] != index {
            let next = if value.path.len() > 0 && value.path[0] > index {
                Record { path: value.path.update(0, value.path[0] - 1), ..value }
            } else { value };
            assert(before.push(next).drop_last() =~= before);
            assert(next.path.len() == value.path.len());
            assert((next.path.len() > 0 && next.path[0] >= 0) == (value.path.len() > 0 && value.path[0] >= 0));
        }
    }
}

/// Updating a root descriptor leaves every nonempty ownership view unchanged.
pub broadcast proof fn select_root(memory: Seq<Record>, root: Record, path: Seq<int>)
    requires root.path == Seq::<int>::empty(), path.len() > 0,
    ensures #[trigger] subtree(memory.push(root), path) == subtree(memory, path),
{
    select_push(memory, root, path);
}

/// Runtime and fixed partitions distribute over composition.
pub broadcast proof fn runtime_add(left: Seq<Record>, right: Seq<Record>)
    ensures #[trigger] runtime(left + right) == runtime(left) + runtime(right),
        nonruntime(left + right) == nonruntime(left) + nonruntime(right),
    decreases right.len(),
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        runtime_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A descriptor belongs to exactly one structural partition.
pub broadcast proof fn runtime_push(memory: Seq<Record>, value: Record)
    ensures #[trigger] runtime(memory.push(value)) ==
        if value.path.len() > 0 && value.path[0] >= 0 { runtime(memory).push(value) } else { runtime(memory) },
        nonruntime(memory.push(value)) ==
        if value.path.len() > 0 && value.path[0] >= 0 { nonruntime(memory) } else { nonruntime(memory).push(value) },
{
    reveal_with_fuel(runtime, 2);
    reveal_with_fuel(nonruntime, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Prefixing an owner places its complete footprint in one structural class.
pub broadcast proof fn runtime_prefix(memory: Seq<Record>, path: Seq<int>)
    requires path.len() > 0,
    ensures #[trigger] runtime(prefix(memory, path)) ==
        if path[0] >= 0 { prefix(memory, path) } else { Seq::<Record>::empty() },
        nonruntime(prefix(memory, path)) ==
        if path[0] >= 0 { Seq::<Record>::empty() } else { prefix(memory, path) },
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
    ensures #[trigger] runtime(runtime(memory)) == runtime(memory),
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

/// Descendant selection distributes over finite forest composition.
pub broadcast proof fn descendants_add(left: Seq<Record>, right: Seq<Record>)
    ensures #[trigger] descendants(left + right) == descendants(left) + descendants(right),
    decreases right.len(),
{
    reveal_with_fuel(descendants, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        descendants_add(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Expose one descriptor's membership in the descendant forest.
pub broadcast proof fn descendants_push(memory: Seq<Record>, value: Record)
    ensures #[trigger] descendants(memory.push(value)) ==
        if value.path.len() == 0 { descendants(memory) } else { descendants(memory).push(value) },
{
    reveal_with_fuel(descendants, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Every allocation below a nonempty prefix is a descendant.
pub broadcast proof fn descendants_prefix(memory: Seq<Record>, path: Seq<int>)
    requires path.len() > 0,
    ensures #[trigger] descendants(prefix(memory, path)) == prefix(memory, path),
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
    requires path.len() > 0,
    ensures #[trigger] subtree(descendants(memory), path) == subtree(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(descendants, 2);
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        select_descendants(memory.drop_last(), path);
        let value = memory.last();
        if value.path.len() > 0 {
            assert(descendants(memory.drop_last()).push(value).drop_last() =~= descendants(memory.drop_last()));
        }
    }
}



/// Joining disjoint owners adds their footprints.
pub broadcast proof fn cost_add(left: Seq<Record>, right: Seq<Record>, kind: int)
    ensures #[trigger] cost(left + right, kind) == cost(left, kind) + cost(right, kind),
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
    ensures #[trigger] cost(memory.push(record), kind) == cost(memory, kind)
        + if record.kind == kind { record.bytes } else { 0 },
{
    reveal(cost);
    assert(memory.push(record).drop_last() =~= memory);
}

/// Moving an owner underneath another value changes paths, not charges.
pub broadcast proof fn cost_prefix(memory: Seq<Record>, path: Seq<int>, kind: int)
    ensures #[trigger] cost(prefix(memory, path), kind) == cost(memory, kind),
    decreases memory.len(),
{
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        cost_prefix(memory.drop_last(), path, kind);
        cost_push(prefix(memory.drop_last(), path), Record {
            path: path + memory.last().path, ..memory.last()
        }, kind);
    }
}

/// Extraction partitions storage exactly; it never copies or loses a charge.
pub proof fn cost_partition(memory: Seq<Record>, path: Seq<int>, kind: int)
    ensures cost(memory, kind)
        == cost(subtree(memory, path), kind) + cost(without(memory, path), kind),
    decreases memory.len(),
{
    reveal_with_fuel(cost, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        cost_partition(memory.drop_last(), path, kind);
        if path.is_prefix_of(memory.last().path) {
            cost_push(subtree(memory.drop_last(), path), Record {
                path: memory.last().path.skip(path.len() as int), ..memory.last()
            }, kind);
        } else { cost_push(without(memory.drop_last(), path), memory.last(), kind); }
    }
}




}
