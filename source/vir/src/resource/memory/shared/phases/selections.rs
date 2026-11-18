//! A popped worker result names exactly one of its candidate allocations.
//! The frozen result identity selects both its backing and any last-drop debit.

use super::{Checkpoint, Handles, RootId, SharedRoots, contracts, unsupported};
use crate::ast::{Expr, VirErr};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct Candidate {
    /// Conditions under which a captured result reaches this allocation.
    pub(super) matches: Vec<Expr>,
    /// Reservations removed if every clone of a captured result has dropped.
    pub(super) released: Option<Expr>,
}

pub(super) type Candidates = BTreeMap<RootId, Candidate>;
pub(super) type Selections = BTreeMap<u64, Handles>;

impl SharedRoots {
    pub(super) fn project_selections(
        &self,
        check: &Checkpoint,
    ) -> Result<(Candidates, Selections), VirErr> {
        let span = &check.site;
        let mut candidates = Candidates::new();
        let mut imports = Selections::new();
        for (id, observed) in &check.selections {
            let alias = self.selections.get(id).ok_or_else(|| {
                unsupported(span, "a worker checkpoint outside its selected result's domain")
            })?;
            let live = observed.in_domain(alias.handles).ok_or_else(|| {
                unsupported(span, "inconsistent checkpoint counts for a selected result")
            })?;
            if let Some(entry) = alias.imported {
                imports.insert(*id, Handles { entry, live });
                continue;
            }
            for root in &alias.roots {
                let candidate = candidates.entry(*root).or_default();
                candidate.matches.push(alias.matches(span, *root));
                if live == 0 {
                    let debit = alias.reservation(span, *root);
                    candidate.released = Some(match candidate.released.take() {
                        Some(prior) => contracts::add(span, prior, debit),
                        None => debit,
                    });
                }
            }
        }
        Ok((candidates, imports))
    }
}
