//! Publication families are static binders; workers are dynamic occurrences.
//!
//! Keep family interning outside cloned ownership states. Revisiting a source
//! site shares a family, but creates another worker. Nested publications also
//! retain their enclosing occurrence, so two parents cannot share child state.

use crate::{
    ast::{Expr, TypX},
    messages::AstId,
};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FamilyId(u64);

/// One publication in a finite ownership state. Symbolic repetitions must bind
/// occurrences within this family, rather than interpreting this registry's
/// length or a single analyzed visit as an executable worker count.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in super::super) struct WorkerId {
    family: FamilyId,
    occurrence: u64,
}

impl WorkerId {
    /// Finite compiler key used as the prefix of a runtime descriptor. Source
    /// loop coordinates are appended by Analysis::worker_identity; this key
    /// alone must never identify every visit to a repeated publication.
    pub(in super::super) fn descriptor(self) -> [i128; 2] {
        [i128::from(self.family.0), i128::from(self.occurrence)]
    }
}

/// A visit to a source site in one actor. The site retains its operation-specific
/// evidence. Publication coordinates precede the actor's own enclosing loops.
#[derive(Clone)]
pub(in super::super) struct SourceVisit<S> {
    /// A source location or a checked native operation at that location.
    pub(in super::super) site: S,
    actor: Option<WorkerId>,
    coordinates: Vec<(AstId, Expr)>,
}

impl super::Analysis<'_> {
    pub(in super::super) fn source_visit<S>(
        &self,
        site: S,
        local: Vec<(AstId, Expr)>,
    ) -> SourceVisit<S> {
        SourceVisit { site, actor: self.current_worker, coordinates: self.actor_coordinates(local) }
    }
}

impl<S> SourceVisit<S> {
    pub(in super::super) fn single_visit(&self) -> bool {
        self.coordinates.is_empty()
    }

    pub(in super::super) fn valid_for(&self, actor: Option<WorkerId>) -> bool {
        self.actor == actor
            && self.coordinates.iter().all(|(_, ordinal)| matches!(&*ordinal.typ, TypX::Int(_)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Site {
    parent: Option<WorkerId>,
    site: AstId,
    closure: usize,
}

/// Compiler-owned static binders, shared by branch/section analysis. Creating a
/// family is not itself a publication and contributes no storage or population.
#[derive(Default)]
pub(in super::super) struct Families {
    sites: BTreeMap<Site, FamilyId>,
}

impl Families {
    pub(in super::super) fn publication(
        &mut self,
        site: AstId,
        closure: usize,
        parent: Option<WorkerId>,
    ) -> WorkerId {
        let family = *self
            .sites
            .entry(Site { parent, site, closure })
            .or_insert_with(|| FamilyId(super::super::accounting::Accounting::fresh_allocation()));
        WorkerId { family, occurrence: super::super::accounting::Accounting::fresh_allocation() }
    }
}
