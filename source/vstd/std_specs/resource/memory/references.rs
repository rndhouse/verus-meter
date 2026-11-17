//! Identity links travel with ownership forests; their targets are charged once
//! by the enclosing accounting domain. These pure descriptors do not establish
//! that an executable handle exists or authorize its creation or destruction.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::forest::{Record, prefix, subtree, without};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Separate identity domains for aliases of shared storage and join handles.
/// An identity can include invocation, worker-family and loop-index binders.
pub enum Reference {
    /// One strong alias. Several records may refer to the same canonical root.
    Shared(Seq<int>),
    /// A handle for one publication; transferring it does not complete the worker.
    Worker(Seq<int>),
}

/// A strong handle's owner node has no separate byte charge. Its inline slot
/// belongs to its containing value, and backing storage belongs to the root.
pub open spec fn shared_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { reference_kind: 1, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// Join-handle ownership names a worker independently of the source handle slot.
pub open spec fn worker_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { reference_kind: 2, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// Query links without adding nested datatype invariants to every byte record.
pub open spec fn refers_to(record: Record, reference: Reference) -> bool {
    match reference {
        Reference::Shared(identity) => record.reference_kind == 1 && record.reference_identity
            == identity,
        Reference::Worker(identity) => record.reference_kind == 2 && record.reference_identity
            == identity,
    }
}

/// Multiplicity includes every alias. It does not assume path or identity
/// uniqueness, and never counts the referenced payload's bytes again.
#[verifier::opaque]
pub open spec fn reference_count(memory: Seq<Record>, reference: Reference) -> int
    decreases memory.len(),
{
    if memory.len() == 0 {
        0
    } else {
        reference_count(memory.drop_last(), reference) + if refers_to(memory.last(), reference) {
            1int
        } else {
            0int
        }
    }
}

/// Concatenation preserves both distinct identities and repeated aliases.
pub proof fn reference_count_add(left: Seq<Record>, right: Seq<Record>, reference: Reference)
    ensures
        reference_count(left + right, reference) == reference_count(left, reference)
            + reference_count(right, reference),
    decreases right.len(),
{
    reveal_with_fuel(reference_count, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        reference_count_add(left, right.drop_last(), reference);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Moving beneath any owner changes only paths, including fixed capture fields
/// and runtime container indices. It cannot clone or retire a target identity.
pub proof fn reference_count_prefix(memory: Seq<Record>, path: Seq<int>, reference: Reference)
    ensures
        reference_count(prefix(memory, path), reference) == reference_count(memory, reference),
    decreases memory.len(),
{
    reveal_with_fuel(reference_count, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        reference_count_prefix(memory.drop_last(), path, reference);
        let mapped = Record { path: path + memory.last().path, ..memory.last() };
        assert(prefix(memory, path).drop_last() =~= prefix(memory.drop_last(), path));
        assert(prefix(memory, path).last() == mapped);
    }
}

/// Extracting one child partitions its reference multiset. The caller must
/// execute actual drop/join effects to retire any extracted references.
pub proof fn reference_count_partition(memory: Seq<Record>, path: Seq<int>, reference: Reference)
    ensures
        reference_count(memory, reference) == reference_count(subtree(memory, path), reference)
            + reference_count(without(memory, path), reference),
    decreases memory.len(),
{
    reveal_with_fuel(reference_count, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        reference_count_partition(memory.drop_last(), path, reference);
        if path.is_prefix_of(memory.last().path) {
            assert(subtree(memory, path).drop_last() =~= subtree(memory.drop_last(), path));
        } else {
            assert(without(memory, path).drop_last() =~= without(memory.drop_last(), path));
        }
    }
}

} // verus!
