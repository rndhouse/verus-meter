//! Fixed heap charges use the normal fixed-byte ledger. Each owning role also
//! names its source allocation. Branches can agree on a role while carrying
//! different constructors; each reaching path keeps its own original identity.

use super::{Accounting, MemoryKind};
use crate::{ast::VirErr, messages::Span, resource::memory::heap::Owner};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in super::super) struct FixedOrigin {
    /// Source construction or checked call result that introduced the charge.
    pub(in super::super) site: u64,
    /// Source-model extent of the original fixed allocation.
    pub(in super::super) bytes: u64,
    /// Only modeled host heap allocations participate in native mutex payload forests.
    pub(in super::super) host_heap: bool,
    /// Fresh analysis binder, instantiated in the enclosing actor and loop visit.
    pub(in super::super) identity: u64,
}

impl super::super::analysis::Analysis<'_> {
    pub(in super::super) fn bind_allocation(&mut self, span: &Span, id: u64) -> Result<(), VirErr> {
        let visit = self.source_visit(span.id, self.local_occurrences(span)?);
        if self.transitions.allocation_visits.insert(id, visit).is_some() {
            return Err(super::unsupported(span, "a duplicate allocation occurrence binder"));
        }
        Ok(())
    }
}

pub(super) type FixedOrigins = BTreeMap<u64, FixedOrigin>;

// Provenance-only identities do not generate SMT locals. Keep their namespace
// separate so attaching an origin cannot rename proof variables or reorder sums.
static NEXT_ORIGIN: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl Accounting {
    pub(in super::super) fn reserve_owned(
        &mut self,
        span: &Span,
        kind: MemoryKind,
        bytes: u64,
        reason: &str,
    ) -> Result<Option<u64>, VirErr> {
        if bytes == 0 {
            return Ok(None);
        }
        let identity =
            NEXT_ORIGIN.fetch_add(1, std::sync::atomic::Ordering::Relaxed) | (1u64 << 62);
        for path in &mut self.paths {
            path.owned.insert(
                identity,
                FixedOrigin {
                    site: span.id,
                    identity,
                    bytes,
                    host_heap: kind == MemoryKind::host_heap(),
                },
            );
        }
        self.reserve(span, kind, bytes, reason)?;
        Ok(Some(identity))
    }

    /// The constructor first observes its explicit reservation, then installs
    /// the vector's persistent backing state. Both describe the same allocation.
    /// Naming the already checked witness preserves its original byte expression.
    pub(in super::super) fn name_vector_reservation(
        &mut self,
        points: std::ops::Range<usize>,
        transient: Option<u64>,
        backing: u64,
    ) {
        for point in &mut std::sync::Arc::make_mut(&mut self.report.points)[points] {
            if let Some(id) = transient {
                point.allocations.remove(&id);
            }
            point.allocations.insert(backing);
        }
    }

    pub(in super::super) fn release_owned(
        &mut self,
        span: &Span,
        role: Option<u64>,
        kind: MemoryKind,
        bytes: u64,
        reason: &str,
    ) {
        if let Some(role) = role {
            for path in &mut self.paths {
                path.owned.remove(&role);
            }
        }
        self.release(span, kind, bytes, reason);
    }

    /// Rename roles simultaneously (two operands may exchange owners). The
    /// origins observed earlier and the actual byte charge stay untouched.
    pub(in super::super) fn align_owned(
        &mut self,
        span: &Span,
        roles: &BTreeMap<u64, u64>,
    ) -> Result<(), VirErr> {
        if roles.is_empty() {
            return Ok(());
        }
        for path in &mut self.paths {
            let mut moved = FixedOrigins::new();
            for (old, new) in roles {
                if let Some(origin) = path.owned.remove(old)
                    && moved.insert(*new, origin).is_some()
                {
                    return Err(super::unsupported(
                        span,
                        "two fixed allocations in one ownership role",
                    ));
                }
            }
            for (role, origin) in moved {
                if path.owned.insert(role, origin).is_some() {
                    return Err(super::unsupported(
                        span,
                        "a fixed allocation already owning its destination role",
                    ));
                }
            }
        }
        Ok(())
    }
}

impl Owner {
    pub(in super::super) fn align_fixed_roles(&self, other: &Self, roles: &mut BTreeMap<u64, u64>) {
        other.visit_paths(&mut Vec::new(), &mut |path, incoming| {
            if let (Some(old), Some(new)) =
                (incoming.fixed_role, self.at(path).and_then(|o| o.fixed_role))
                && old != new
            {
                roles.insert(old, new);
            }
        });
    }
}

impl super::Live {
    pub(super) fn fixed_origins(&self) -> BTreeSet<FixedOrigin> {
        self.owned.values().copied().collect()
    }
}

/// Disjoint storage at the fixed ownership paths of one reaching return. A
/// dynamic ID can name a forest charge. Its constituents are interpreted by
/// the checked transfer template, never as one fresh executable allocation.
#[derive(Clone, Default)]
pub(in super::super) struct ReturnedStorage {
    nodes: BTreeMap<super::super::heap::OwnerPath, BTreeSet<ReturnedRegion>>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ReturnedRegion {
    Fixed(FixedOrigin),
    Dynamic(u64),
    Input(usize),
}

impl Accounting {
    /// Preserve branch alternatives instead of attributing an adopted result
    /// to a single constructor chosen from several return edges.
    pub(in super::super) fn returned_storage(
        &self,
        owner: Option<&Owner>,
        elements: &[super::super::elements::ElementState],
    ) -> Vec<ReturnedStorage> {
        let Some(owner) = owner else { return Vec::new() };
        self.paths
            .iter()
            .map(|path| {
                let mut output = ReturnedStorage::default();
                owner.visit_paths(&mut Vec::new(), &mut |location, node| {
                    let mut regions = BTreeSet::new();
                    if let Some(origin) = node.fixed_role.and_then(|role| path.owned.get(&role)) {
                        regions.insert(ReturnedRegion::Fixed(*origin));
                    }
                    if let Some(input) = node.input {
                        regions.insert(ReturnedRegion::Input(input));
                    }
                    if let Some(id) = node.dynamic.filter(|id| path.dynamic.contains_key(id)) {
                        regions.insert(ReturnedRegion::Dynamic(id));
                    }
                    if let Some(children) = &node.elements {
                        regions.extend(children.inputs.iter().copied().map(ReturnedRegion::Input));
                        regions.extend(
                            children
                                .states
                                .values()
                                .map(|id| elements[*id].id)
                                .filter(|id| path.dynamic.contains_key(id))
                                .map(ReturnedRegion::Dynamic),
                        );
                    }
                    output.nodes.insert(location.clone(), regions);
                });
                output
            })
            .collect()
    }
}

impl ReturnedStorage {
    /// A replacement in another ledger must be justified on every reaching
    /// path. A byte-identical alternative with another origin stays charged.
    pub(in crate::resource::memory) fn common_payload_ids(views: &[Self]) -> BTreeSet<u64> {
        let physical = |view: &Self| -> BTreeSet<_> {
            view.nodes
                .values()
                .flatten()
                .filter_map(|region| match region {
                    ReturnedRegion::Dynamic(id) => Some(*id),
                    ReturnedRegion::Fixed(origin) if origin.host_heap => Some(origin.identity),
                    _ => None,
                })
                .collect()
        };
        let Some((first, others)) = views.split_first() else { return BTreeSet::new() };
        let mut ids = physical(first);
        for view in others {
            let alternative = physical(view);
            ids.retain(|id| alternative.contains(id));
        }
        ids
    }

    pub(in crate::resource::memory) fn dynamic_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.nodes.values().flatten().filter_map(|region| match region {
            ReturnedRegion::Dynamic(id) => Some(*id),
            _ => None,
        })
    }

    /// A caller may materialize a summary charge and split its forest. Its
    /// structural result path must exist in the callee's checked output or
    /// have an explicit projected node in a checked runtime forest.
    pub(in super::super) fn validate_against(
        &self,
        callee: &[Self],
        has_template: bool,
        span: &Span,
    ) -> Result<(), VirErr> {
        for (path, regions) in &self.nodes {
            if !regions.is_empty()
                && !callee.iter().any(|output| output.nodes.contains_key(path))
                && !has_template
            {
                return Err(super::unsupported(
                    span,
                    "a returned charge without its helper output path",
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{messages::Span, resource::memory::contracts};
    use std::sync::Arc;

    fn span(id: u64) -> Span {
        Span { raw_span: Arc::new(()), id, data: Arc::new([]), as_string: "fixed ownership".into() }
    }

    #[test]
    fn equal_sized_branch_results_retain_their_distinct_constructors() {
        let site = span(1);
        let mut left = Accounting::new(&site, 64);
        let mut right = left.clone();
        let role =
            left.reserve_owned(&site, MemoryKind::host_heap(), 32, "left box").unwrap().unwrap();
        let other = right
            .reserve_owned(&span(2), MemoryKind::host_heap(), 32, "right box")
            .unwrap()
            .unwrap();
        right.align_owned(&span(3), &[(other, role)].into()).unwrap();
        left.join_live(&right).unwrap();
        left.record_live(&span(3)).unwrap();
        let alternatives: Vec<_> =
            left.points().iter().filter(|point| point.span.id == 3).collect();
        assert_eq!(alternatives.len(), 2);
        for (phase, original) in alternatives.iter().zip([role, other]) {
            assert_eq!(contracts::constant(&phase.cost.total()), Some(32));
            assert_eq!(phase.fixed_origins.len(), 1);
            assert_eq!(phase.fixed_origins.first().unwrap().identity, original);
        }
        let returned = Owner { fixed_role: Some(role), bytes: 32, ..Owner::default() };
        let outputs = left.returned_storage(Some(&returned), &[]);
        assert_eq!(outputs.len(), 2);
        for (output, original) in outputs.iter().zip([role, other]) {
            let [ReturnedRegion::Fixed(source)] =
                output.nodes[&Vec::new()].iter().collect::<Vec<_>>()[..]
            else {
                panic!("each returned box has one source allocation");
            };
            assert_eq!(source.identity, original);
        }
        left.release_owned(&span(4), Some(role), MemoryKind::host_heap(), 32, "merged result");
        left.check_transferred(&span(4)).unwrap();
    }
}
