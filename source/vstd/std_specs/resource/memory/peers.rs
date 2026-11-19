//! Backing retained after the carrying result drops before its allocation peers.
use crate::prelude::*;

verus! {

broadcast use crate::seq::group_seq_axioms;

/// One deferred charge, keyed by the full identity of an allocation visit.
pub struct DeferredBacking {
    /// Immutable identity recorded by construction, publication and join.
    pub visit: Seq<int>,
    /// Original backing extent, including the control block and owned storage.
    pub bytes: nat,
    /// Checked upper bound on reservations that still retain this backing.
    pub peers: int,
}

/// Charge every retained allocation once, even when extents coincide.
pub open spec fn deferred_bytes(entries: Seq<DeferredBacking>) -> int
    decreases entries.len(),
{
    if entries.len() == 0 {
        0
    } else {
        deferred_bytes(entries.drop_last()) + entries.last().bytes
    }
}

/// Ending a carrier defers its extent only while a peer may retain it.
pub open spec fn defer_backing(
    entries: Seq<DeferredBacking>,
    visit: Seq<int>,
    bytes: int,
    peers: int,
) -> Seq<DeferredBacking> {
    if peers > 0 && bytes > 0 {
        entries.push(DeferredBacking { visit, bytes: bytes as nat, peers })
    } else {
        entries
    }
}

/// Retire one actual reservation on its own visit. Other allocations, including
/// equal-sized allocations from this constructor, retain their entire charge.
pub open spec fn retire_peer(entries: Seq<DeferredBacking>, visit: Seq<int>) -> Seq<DeferredBacking>
    decreases entries.len(),
{
    if entries.len() == 0 {
        entries
    } else {
        let last = entries.last();
        let rest = retire_peer(entries.drop_last(), visit);
        if last.visit != visit {
            rest.push(last)
        } else if last.peers > 1 {
            rest.push(DeferredBacking { peers: last.peers - 1, ..last })
        } else {
            rest
        }
    }
}

/// A retired reservation discharges its own visit. If this was the last
/// reservation across all visits, even conservative per-visit bounds expire.
pub open spec fn finish_peer_backing(
    entries: Seq<DeferredBacking>,
    visit: Seq<int>,
    bytes: int,
    remaining: int,
    retired: int,
    pending: int,
) -> Seq<DeferredBacking> {
    if pending == retired {
        Seq::empty()
    } else if retired == 0 {
        defer_backing(entries, visit, bytes, remaining)
    } else {
        retire_peer(entries, visit)
    }
}

/// Reduce the byte sum over a concrete push without unfolding the history.
pub broadcast proof fn deferred_push(entries: Seq<DeferredBacking>, entry: DeferredBacking)
    ensures
        #[trigger] deferred_bytes(entries.push(entry)) == deferred_bytes(entries) + entry.bytes,
{
    assert(entries.push(entry).drop_last() =~= entries);
}

/// Retiring one visit can never increase the sum, including when other
/// visits with identical extents still have outstanding reservations.
proof fn retire_bytes(entries: Seq<DeferredBacking>, visit: Seq<int>)
    ensures
        0 <= deferred_bytes(retire_peer(entries, visit)) <= deferred_bytes(entries),
    decreases entries.len(),
{
    if entries.len() > 0 {
        let rest = entries.drop_last();
        let last = entries.last();
        retire_bytes(rest, visit);
        if last.visit != visit {
            deferred_push(retire_peer(rest, visit), last);
        } else if last.peers > 1 {
            deferred_push(
                retire_peer(rest, visit),
                DeferredBacking { peers: last.peers - 1, ..last },
            );
        }
    }
}

/// Only a carrying result can add bytes. A peer may release its own visit
/// or leave its extent unchanged when other peers survive.
pub broadcast proof fn finish_peer_bound(
    entries: Seq<DeferredBacking>,
    visit: Seq<int>,
    bytes: int,
    remaining: int,
    retired: int,
    pending: int,
)
    ensures
        0 <= deferred_bytes(entries),
        deferred_bytes(
            #[trigger] finish_peer_backing(entries, visit, bytes, remaining, retired, pending),
        ) <= deferred_bytes(entries) + if retired == 0 && bytes > 0 {
            bytes
        } else {
            0
        },
{
    retire_bytes(entries, visit);
    if remaining > 0 && bytes > 0 {
        deferred_push(entries, DeferredBacking { visit, bytes: bytes as nat, peers: remaining });
    }
}

/// Reduce a retirement over one stored visit, preserving the other entries.
pub broadcast proof fn retire_push(
    entries: Seq<DeferredBacking>,
    entry: DeferredBacking,
    visit: Seq<int>,
)
    ensures
        #[trigger] retire_peer(entries.push(entry), visit) == (if entry.visit != visit {
            retire_peer(entries, visit).push(entry)
        } else if entry.peers > 1 {
            retire_peer(entries, visit).push(DeferredBacking { peers: entry.peers - 1, ..entry })
        } else {
            retire_peer(entries, visit)
        }),
{
    assert(entries.push(entry).drop_last() =~= entries);
}

/// A worker consuming a captured strong handle has no returned link. Reading
/// the prefixed capture still identifies the very same allocation.
pub broadcast proof fn captured_visit(path: Seq<int>, visit: Seq<int>)
    ensures
        #[trigger] super::forest::lookup(
            super::forest::prefix(
                seq![super::references::shared_reference(Seq::empty(), visit)],
                path,
            ),
            path,
        ).reference_identity == visit,
{
    let memory = seq![super::references::shared_reference(Seq::empty(), visit)];
    let root = super::references::shared_reference(Seq::empty(), visit);
    assert(memory =~= Seq::empty().push(root));
    super::selection::lookup_push(Seq::empty(), root, Seq::empty());
    assert(path.is_prefix_of(path));
    super::selection::lookup_prefix(memory, path, path);
    assert(path.skip(path.len() as int) =~= Seq::<int>::empty());
}

pub broadcast group group_deferred_backings {
    captured_visit,
    deferred_push,
    retire_push,
}

} // verus!
