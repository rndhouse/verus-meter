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
    request_add,
    request_push,
    request_runtime,
    request_nonruntime,
    request_descendants,
    request_without,
    request_subtree,
    request_prefix,
    request_shift,
    request_tile,
    request_generate,
    request_reverse,
    request_take,
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

/// Move a runtime interval to consecutive destination indices in reverse order.
/// The nested descriptors and their byte extents are preserved independently of
/// the element layout; repeated pops followed by pushes induce this map.
#[verifier::opaque]
pub open spec fn reverse_children(memory: Seq<Record>, start: int, end: int, base: int) -> Seq<Record>
    decreases memory.len(),
{
    if memory.len() == 0 { Seq::empty() } else {
        let before = reverse_children(memory.drop_last(), start, end, base);
        let value = memory.last();
        if value.path.len() > 0 && 0 <= value.path[0] && start <= value.path[0] < end {
            before.push(Record { path: value.path.update(0, base + end - 1 - value.path[0]), ..value })
        } else { before }
    }
}

/// Range transfer preserves validity and never invents allocation bytes.
pub proof fn reverse_children_facts(memory: Seq<Record>, start: int, end: int, base: int)
    requires well_formed(memory), base >= 0,
    ensures well_formed(reverse_children(memory, start, end, base)),
        0 <= cost(reverse_children(memory, start, end, base), 0) <= cost(memory, 0),
        runtime(reverse_children(memory, start, end, base)) == reverse_children(memory, start, end, base),
        nonruntime(reverse_children(memory, start, end, base)) == Seq::<Record>::empty(),
        descendants(reverse_children(memory, start, end, base)) == reverse_children(memory, start, end, base),
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
            let mapped = Record { path: value.path.update(0, base + end - 1 - value.path[0]), ..value };
            assert(before.push(mapped).drop_last() =~= before);
            runtime_push(before, mapped);
            descendants_push(before, mapped);
        }
    }
}

/// A verified matching gate for precise indexed views. It is always true, but
/// remains opaque so constructor facts activate only for requested paths.
#[verifier::opaque]
pub open spec fn view_requested(memory: Seq<Record>, index: int) -> bool {
    true
}

/// Request the outer indexed view needed by a concrete projection.
pub proof fn request_path(memory: Seq<Record>, path: Seq<int>)
    ensures
        path.len() > 0 ==> view_requested(memory, path[0]),
{
    reveal(view_requested);
}

/// Requests follow the two operands of a composed forest.
pub broadcast proof fn request_add(left: Seq<Record>, right: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(left + right, index) ==> view_requested(left, index)
            && view_requested(right, index),
{
    reveal(view_requested);
}

/// A root descriptor does not hide its descendants' indexed views.
pub broadcast proof fn request_push(memory: Seq<Record>, value: Record, index: int)
    ensures
        #[trigger] view_requested(memory.push(value), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Runtime filtering preserves indexed requests.
pub broadcast proof fn request_runtime(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(runtime(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Fixed filtering preserves the source of a projected view.
pub broadcast proof fn request_nonruntime(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(nonruntime(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Descendant filtering preserves the source of a projected view.
pub broadcast proof fn request_descendants(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(descendants(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Excluding a subtree retains the original forest's sibling views.
pub broadcast proof fn request_without(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(without(memory, path), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// A nested projection first needs the selected enclosing child.
pub broadcast proof fn request_subtree(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(subtree(memory, path), index) ==> if path.len() > 0 {
            view_requested(memory, path[0])
        } else {
            view_requested(memory, index)
        },
{
    reveal(view_requested);
}

/// Prefixing a forest retains requests for the underlying descriptors.
pub broadcast proof fn request_prefix(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(prefix(memory, path), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// A shifted slot requests its original index.
pub broadcast proof fn request_shift(memory: Seq<Record>, base: int, index: int)
    ensures
        #[trigger] view_requested(shift_children(memory, base), index) ==> view_requested(
            memory,
            index - base,
        ),
{
    reveal(view_requested);
}

/// A tiled slot requests the corresponding position inside its block.
pub broadcast proof fn request_tile(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    ensures
        #[trigger] view_requested(tile_children(block, width, count, start), index) ==> (width > 0
            ==> view_requested(block, (index - start) % width)),
{
    reveal(view_requested);
}

/// A generated slot requests the corresponding child in its iteration block.
pub broadcast proof fn request_generate(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    ensures
        #[trigger] view_requested(generate_children(builder, width, count, start), index) ==> (width
            > 0 ==> view_requested(builder((index - start) / width), (index - start) % width)),
{
    reveal(view_requested);
}

/// Reversed slots request their source child through the inverse range map.
pub broadcast proof fn request_reverse(
    memory: Seq<Record>,
    start: int,
    end: int,
    base: int,
    index: int,
)
    ensures
        #[trigger] view_requested(reverse_children(memory, start, end, base), index)
            ==> view_requested(memory, base + end - 1 - index),
{
    reveal(view_requested);
}

/// Prefix retention keeps the original child views.
pub broadcast proof fn request_take(memory: Seq<Record>, length: int, index: int)
    ensures
        #[trigger] view_requested(take_children(memory, length), index) ==> view_requested(
            memory,
            index,
        ),
{
    reveal(view_requested);
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

/// Expose finite caller descriptors without unfolding recursive range transfers.
pub broadcast proof fn reverse_children_push(memory: Seq<Record>, value: Record, start: int, end: int, base: int)
    ensures #[trigger] reverse_children(memory.push(value), start, end, base) ==
        if value.path.len() > 0 && 0 <= value.path[0] && start <= value.path[0] < end {
            reverse_children(memory, start, end, base).push(Record {
                path: value.path.update(0, base + end - 1 - value.path[0]), ..value
            })
        } else { reverse_children(memory, start, end, base) },
{
    reveal_with_fuel(reverse_children, 2);
    assert(memory.push(value).drop_last() =~= memory);
}

/// Range transfer distributes over disjoint contributions to a forest.
pub broadcast proof fn reverse_children_add(left: Seq<Record>, right: Seq<Record>, start: int, end: int, base: int)
    ensures #[trigger] reverse_children(left + right, start, end, base) ==
        reverse_children(left, start, end, base) + reverse_children(right, start, end, base),
    decreases right.len(),
{
    reveal_with_fuel(reverse_children, 2);
    if right.len() == 0 { assert(left + right =~= left); }
    else {
        reverse_children_add(left, right.drop_last(), start, end, base);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A selected child keeps its entire nested forest at the mapped destination.
pub broadcast proof fn reverse_children_prefix(memory: Seq<Record>, path: Seq<int>, start: int, end: int, base: int)
    requires path.len() > 0,
    ensures #[trigger] reverse_children(prefix(memory, path), start, end, base) ==
        if 0 <= path[0] && start <= path[0] < end {
            prefix(memory, path.update(0, base + end - 1 - path[0]))
        } else { Seq::<Record>::empty() },
    decreases memory.len(),
{
    reveal_with_fuel(reverse_children, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        reverse_children_prefix(memory.drop_last(), path, start, end, base);
        let before = prefix(memory.drop_last(), path);
        let value = Record { path: path + memory.last().path, ..memory.last() };
        assert(before.push(value).drop_last() =~= before);
        assert((path + memory.last().path).update(0, base + end - 1 - path[0]) =~=
            path.update(0, base + end - 1 - path[0]) + memory.last().path);
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

/// Repeat an ordered block of runtime children, flattening its logical indices.
/// Width counts occupied children independently of the block's allocation cost.
#[verifier::opaque]
pub open spec fn tile_children(block: Seq<Record>, width: int, count: int, start: int) -> Seq<
    Record,
>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        tile_children(block, width, count - 1, start) + shift_children(
            block,
            start + width * (count - 1),
        )
    }
}

/// Block repetition preserves every child descriptor and has additive cost.
pub proof fn tile_children_facts(block: Seq<Record>, width: int, count: int, start: int)
    requires
        well_formed(block),
        width >= 0,
        count >= 0,
        start >= 0,
        runtime(block) == block,
    ensures
        well_formed(tile_children(block, width, count, start)),
        cost(tile_children(block, width, count, start), 0) == count * cost(block, 0),
        runtime(tile_children(block, width, count, start)) == tile_children(
            block,
            width,
            count,
            start,
        ),
        nonruntime(tile_children(block, width, count, start)) == Seq::<Record>::empty(),
        descendants(tile_children(block, width, count, start)) == tile_children(
            block,
            width,
            count,
            start,
        ),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        tile_children_facts(block, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(width * (count - 1) >= 0) by (nonlinear_arith)
            requires
                width >= 0,
                count > 0,
        ;
        assert(base >= 0);
        shift_children_facts(block, base);
        let before = tile_children(block, width, count - 1, start);
        let next = shift_children(block, base);
        well_formed_add(before, next);
        cost_add(before, next, 0);
        runtime_add(before, next);
        runtime_class(next);
        descendants_add(before, next);
        assert((count - 1) * cost(block, 0) + cost(block, 0) == count * cost(block, 0))
            by (nonlinear_arith);
        assert(cost(before, 0) + cost(next, 0) == count * cost(block, 0));
    } else {
        cost_empty(0);
    }
}

/// Generate a complete block for each iteration, preserving nonuniform children.
/// Logical width describes occupied slots independently of their allocation sizes.
#[verifier::opaque]
pub open spec fn generate_children(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
) -> Seq<Record>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        generate_children(builder, width, count - 1, start) + shift_children(
            builder(count - 1),
            start + width * (count - 1),
        )
    }
}

/// Sum the actual footprint of every generated block, without a uniform bound.
#[verifier::opaque]
pub open spec fn generated_cost(builder: spec_fn(int) -> Seq<Record>, count: int) -> int
    decreases count,
{
    if count <= 0 {
        0
    } else {
        generated_cost(builder, count - 1) + cost(builder(count - 1), 0)
    }
}

/// Sum an affine footprint over any number of generated iterations. Doubling
/// the sum avoids division and preserves an exact integer equality.
pub proof fn generated_cost_affine(
    builder: spec_fn(int) -> Seq<Record>,
    count: int,
    slope: int,
    intercept: int,
)
    requires
        count >= 0,
        forall|k: int| 0 <= k < count ==> cost(#[trigger] builder(k), 0) == slope * k + intercept,
    ensures
        2 * generated_cost(builder, count) == slope * count * (count - 1) + 2 * intercept * count,
    decreases count,
{
    reveal_with_fuel(generated_cost, 2);
    if count > 0 {
        generated_cost_affine(builder, count - 1, slope, intercept);
        let previous = generated_cost(builder, count - 1);
        let current = generated_cost(builder, count);
        assert(2 * current == slope * count * (count - 1) + 2 * intercept * count)
            by (nonlinear_arith)
            requires
                2 * previous == slope * (count - 1) * (count - 2) + 2 * intercept * (count - 1),
                current == previous + slope * (count - 1) + intercept,
        ;
    } else {
        assert(slope * count * (count - 1) + 2 * intercept * count == 0) by (nonlinear_arith)
            requires
                count == 0,
        ;
    }
}

/// Generation preserves validity and adds the exact costs of different blocks.
pub proof fn generate_children_facts(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        width >= 0,
        count >= 0,
        start >= 0,
        forall|k: int| 0 <= k < count ==> well_formed(#[trigger] builder(k)),
        forall|k: int| 0 <= k < count ==> runtime(#[trigger] builder(k)) == builder(k),
    ensures
        well_formed(generate_children(builder, width, count, start)),
        cost(generate_children(builder, width, count, start), 0) == generated_cost(builder, count),
        runtime(generate_children(builder, width, count, start)) == generate_children(
            builder,
            width,
            count,
            start,
        ),
        nonruntime(generate_children(builder, width, count, start)) == Seq::<Record>::empty(),
        descendants(generate_children(builder, width, count, start)) == generate_children(
            builder,
            width,
            count,
            start,
        ),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    reveal_with_fuel(generated_cost, 2);
    if count > 0 {
        generate_children_facts(builder, width, count - 1, start);
        let block = builder(count - 1);
        let base = start + width * (count - 1);
        assert(base >= 0) by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        shift_children_facts(block, base);
        let before = generate_children(builder, width, count - 1, start);
        let next = shift_children(block, base);
        well_formed_add(before, next);
        cost_add(before, next, 0);
        runtime_add(before, next);
        runtime_class(next);
        descendants_add(before, next);
    } else {
        cost_empty(0);
    }
}

/// Every descriptor in an ordered block belongs to one occupied runtime slot.
pub open spec fn block_bounds(memory: Seq<Record>, width: int) -> bool
    decreases memory.len(),
{
    memory.len() == 0 || (block_bounds(memory.drop_last(), width) && memory.last().path.len() > 0
        && 0 <= memory.last().path[0] < width)
}

/// A complete child occupies one declared slot in a block.
pub proof fn block_bounds_prefix(child: Seq<Record>, index: int, width: int)
    requires
        0 <= index < width,
    ensures
        block_bounds(prefix(child, seq![index]), width),
    decreases child.len(),
{
    reveal_with_fuel(prefix, 2);
    if child.len() > 0 {
        block_bounds_prefix(child.drop_last(), index, width);
        let before = prefix(child.drop_last(), seq![index]);
        let value = Record { path: seq![index] + child.last().path, ..child.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Composing forests preserves their common logical block extent.
pub proof fn block_bounds_add(left: Seq<Record>, right: Seq<Record>, width: int)
    requires
        block_bounds(left, width),
        block_bounds(right, width),
    ensures
        block_bounds(left + right, width),
    decreases right.len(),
{
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        block_bounds_add(left, right.drop_last(), width);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A wider logical extent still contains every descriptor.
pub proof fn block_bounds_weaken(memory: Seq<Record>, from: int, to: int)
    requires
        block_bounds(memory, from),
        from <= to,
    ensures
        block_bounds(memory, to),
    decreases memory.len(),
{
    if memory.len() > 0 {
        block_bounds_weaken(memory.drop_last(), from, to);
    }
}

/// Translating runtime indices translates the block extent.
pub proof fn block_bounds_shift(memory: Seq<Record>, width: int, base: int)
    requires
        block_bounds(memory, width),
        base >= 0,
    ensures
        block_bounds(shift_children(memory, base), base + width),
    decreases memory.len(),
{
    reveal_with_fuel(shift_children, 2);
    if memory.len() > 0 {
        block_bounds_shift(memory.drop_last(), width, base);
        let before = shift_children(memory.drop_last(), base);
        let value = Record {
            path: memory.last().path.update(0, memory.last().path[0] + base),
            ..memory.last()
        };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Consecutive copies remain inside the declared logical extent.
pub proof fn block_bounds_repeat(child: Seq<Record>, start: int, count: int, width: int)
    requires
        start >= 0,
        count >= 0,
        start + count <= width,
    ensures
        block_bounds(repeat(child, start, count), width),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    if count > 0 {
        block_bounds_repeat(child, start, count - 1, width);
        block_bounds_prefix(child, start + count - 1, width);
        block_bounds_add(
            repeat(child, start, count - 1),
            prefix(child, seq![start + count - 1]),
            width,
        );
    }
}

/// Flattened repeated blocks occupy their combined logical extent.
pub proof fn block_bounds_tile(block: Seq<Record>, width: int, count: int, start: int)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        block_bounds(tile_children(block, width, count, start), start + width * count),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        block_bounds_tile(block, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        block_bounds_weaken(
            tile_children(block, width, count - 1, start),
            base,
            start + width * count,
        );
        block_bounds_shift(block, width, base);
        block_bounds_add(
            tile_children(block, width, count - 1, start),
            shift_children(block, base),
            start + width * count,
        );
    }
}

/// Indices outside a block select no child allocations.
pub proof fn block_bounds_empty_selection(memory: Seq<Record>, width: int, index: int)
    requires
        block_bounds(memory, width),
        index < 0 || index >= width,
    ensures
        subtree(memory, seq![index]) == Seq::<Record>::empty(),
    decreases memory.len(),
{
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        block_bounds_empty_selection(memory.drop_last(), width, index);
        slot_prefix(index, memory.last().path);
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

/// Indices outside the repeated block range select an empty forest.
pub proof fn tile_children_outside(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
        index < start || index >= start + width * count,
    ensures
        subtree(tile_children(block, width, count, start), seq![index]) == Seq::<Record>::empty(),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        tile_children_outside(block, width, count - 1, start, index);
        shift_children_select(block, width, base, index);
        block_bounds_empty_selection(block, width, index - base);
        select_add(
            tile_children(block, width, count - 1, start),
            shift_children(block, base),
            seq![index],
        );
    } else {
        select_empty(seq![index]);
    }
}

/// Select one logical slot without expanding the number of repetitions.
pub proof fn tile_children_at(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    iteration: int,
    offset: int,
)
    requires
        block_bounds(block, width),
        width > 0,
        count >= 0,
        start >= 0,
        0 <= iteration < count,
        0 <= offset < width,
    ensures
        subtree(tile_children(block, width, count, start), seq![start + width * iteration + offset])
            == subtree(block, seq![offset]),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    let index = start + width * iteration + offset;
    let base = start + width * (count - 1);
    assert(base >= 0) by (nonlinear_arith)
        requires
            start >= 0,
            width > 0,
            count > 0,
            base == start + width * (count - 1),
    ;
    shift_children_select(block, width, base, index);
    select_add(
        tile_children(block, width, count - 1, start),
        shift_children(block, base),
        seq![index],
    );
    if iteration == count - 1 {
        assert(index == base + offset) by (nonlinear_arith)
            requires
                iteration == count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        tile_children_outside(block, width, count - 1, start, index);
    } else {
        tile_children_at(block, width, count - 1, start, iteration, offset);
        assert(index - base < 0) by (nonlinear_arith)
            requires
                width > 0,
                0 <= offset < width,
                iteration < count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        block_bounds_empty_selection(block, width, index - base);
    }
}

/// Exact indexed views avoid expanding a runtime number of blocks at callers.
pub proof fn tile_children_views(block: Seq<Record>, width: int, count: int, start: int)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        forall|index: int|
            #![trigger view_requested(tile_children(block, width, count, start), index), subtree(tile_children(block, width, count, start), seq![index])]
            view_requested(tile_children(block, width, count, start), index) ==> (subtree(
                tile_children(block, width, count, start),
                seq![index],
            ) == if width > 0 && start <= index < start + width * count {
                subtree(block, seq![(index - start) % width])
            } else {
                Seq::<Record>::empty()
            }),
{
    assert forall|index: int|
        #![trigger view_requested(tile_children(block, width, count, start), index), subtree(tile_children(block, width, count, start), seq![index])]
        view_requested(tile_children(block, width, count, start), index) ==> (subtree(
            tile_children(block, width, count, start),
            seq![index],
        ) == if width > 0 && start <= index < start + width * count {
            subtree(block, seq![(index - start) % width])
        } else {
            Seq::<Record>::empty()
        }) by {
        if width > 0 && start <= index < start + width * count {
            let x = index - start;
            let k = x / width;
            let r = x % width;
            crate::arithmetic::div_mod::lemma_fundamental_div_mod(x, width);
            crate::arithmetic::div_mod::lemma_mod_pos_bound(x, width);
            assert(0 <= k < count) by (nonlinear_arith)
                requires
                    x == width * k + r,
                    0 <= r < width,
                    width > 0,
                    0 <= x < width * count,
            ;
            tile_children_at(block, width, count, start, k, r);
            assert(index == start + width * k + r);
        } else {
            tile_children_outside(block, width, count, start, index);
        }
    }
}

/// Flattened repeated blocks occupy their combined logical extent.
pub proof fn block_bounds_generate(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        block_bounds(generate_children(builder, width, count, start), start + width * count),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    if count > 0 {
        block_bounds_generate(builder, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        block_bounds_weaken(
            generate_children(builder, width, count - 1, start),
            base,
            start + width * count,
        );
        block_bounds_shift(builder(count - 1), width, base);
        block_bounds_add(
            generate_children(builder, width, count - 1, start),
            shift_children(builder(count - 1), base),
            start + width * count,
        );
    }
}

/// Indices outside the repeated block range select an empty forest.
pub proof fn generate_children_outside(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
        index < start || index >= start + width * count,
    ensures
        subtree(generate_children(builder, width, count, start), seq![index]) == Seq::<
            Record,
        >::empty(),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    if count > 0 {
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        generate_children_outside(builder, width, count - 1, start, index);
        shift_children_select(builder(count - 1), width, base, index);
        block_bounds_empty_selection(builder(count - 1), width, index - base);
        select_add(
            generate_children(builder, width, count - 1, start),
            shift_children(builder(count - 1), base),
            seq![index],
        );
    } else {
        select_empty(seq![index]);
    }
}

/// Select one logical slot without expanding the number of repetitions.
pub proof fn generate_children_at(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    iteration: int,
    offset: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width > 0,
        count >= 0,
        start >= 0,
        0 <= iteration < count,
        0 <= offset < width,
    ensures
        subtree(
            generate_children(builder, width, count, start),
            seq![start + width * iteration + offset],
        ) == subtree(builder(iteration), seq![offset]),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    let index = start + width * iteration + offset;
    let base = start + width * (count - 1);
    assert(base >= 0) by (nonlinear_arith)
        requires
            start >= 0,
            width > 0,
            count > 0,
            base == start + width * (count - 1),
    ;
    shift_children_select(builder(count - 1), width, base, index);
    select_add(
        generate_children(builder, width, count - 1, start),
        shift_children(builder(count - 1), base),
        seq![index],
    );
    if iteration == count - 1 {
        assert(index == base + offset) by (nonlinear_arith)
            requires
                iteration == count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        generate_children_outside(builder, width, count - 1, start, index);
    } else {
        generate_children_at(builder, width, count - 1, start, iteration, offset);
        assert(index - base < 0) by (nonlinear_arith)
            requires
                width > 0,
                0 <= offset < width,
                iteration < count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        block_bounds_empty_selection(builder(count - 1), width, index - base);
    }
}

/// Exact indexed views avoid expanding a runtime number of blocks at callers.
pub proof fn generate_children_views(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        forall|index: int|
            #![trigger view_requested(generate_children(builder, width, count, start), index), subtree(generate_children(builder, width, count, start), seq![index])]
            view_requested(generate_children(builder, width, count, start), index) ==> (subtree(
                generate_children(builder, width, count, start),
                seq![index],
            ) == if width > 0 && start <= index < start + width * count {
                subtree(builder((index - start) / width), seq![(index - start) % width])
            } else {
                Seq::<Record>::empty()
            }),
{
    assert forall|index: int|
        #![trigger view_requested(generate_children(builder, width, count, start), index), subtree(generate_children(builder, width, count, start), seq![index])]
        view_requested(generate_children(builder, width, count, start), index) ==> (subtree(
            generate_children(builder, width, count, start),
            seq![index],
        ) == if width > 0 && start <= index < start + width * count {
            subtree(builder((index - start) / width), seq![(index - start) % width])
        } else {
            Seq::<Record>::empty()
        }) by {
        if width > 0 && start <= index < start + width * count {
            let x = index - start;
            let k = x / width;
            let r = x % width;
            crate::arithmetic::div_mod::lemma_fundamental_div_mod(x, width);
            crate::arithmetic::div_mod::lemma_mod_pos_bound(x, width);
            assert(0 <= k < count) by (nonlinear_arith)
                requires
                    x == width * k + r,
                    0 <= r < width,
                    width > 0,
                    0 <= x < width * count,
            ;
            generate_children_at(builder, width, count, start, k, r);
            assert(index == start + width * k + r);
        } else {
            generate_children_outside(builder, width, count, start, index);
        }
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
