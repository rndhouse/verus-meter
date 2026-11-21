//! Describe one mutex critical section from its worker body before composing histories.

use super::{
    Binding, Interval,
    recipe::{Position, Recipe, Schedule},
};
use crate::{
    ast::VarIdent,
    resource::memory::{growth::Growth, workers::execution::Execution},
};
use std::collections::HashMap;

/// How one acquisition observes, releases and returns protected storage.
pub(super) struct Section<'a> {
    /// Worker whose executable body supplies the effects.
    pub(super) worker: &'a Execution,
    /// Source position where the worker snapshots the incoming contents.
    pub(super) access: Position,
    /// Guard acquisition that authorizes this section.
    pub(super) interval: Interval,
    /// Incoming contents and release snapshots for the same acquisition.
    pub(super) binding: &'a Binding,
    /// One body-derived transformation per possible release of the guard.
    pub(super) releases: Vec<Recipe>,
    /// One source-checked result per normal return of a returning holder.
    pub(super) returns: Vec<Recipe>,
}

impl<'a> Section<'a> {
    /// A fixed section needs one source visit and complete contents at each
    /// release. Its symbolic effects can use immutable publisher inputs captured
    /// by the worker.
    pub(super) fn from_worker(
        growth: &Growth,
        worker: &'a Execution,
        interval: Interval,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Option<Self> {
        let effects = &worker.effects.ownership;
        let binding = &effects.protected_versions.bindings[&interval];
        if !effects.fixed_acquisition(interval)
            || !binding.access.single_visit()
            || !binding.releases.iter().all(|r| r.complete && r.visit.single_visit())
        {
            return None;
        }
        let schedule = Schedule::for_body(growth, &worker.effects.body);
        let captures = worker
            .immutable_scalars
            .iter()
            .filter(|(_, n)| parameters.contains_key(*n))
            .map(|(local, formal)| (local.clone(), formal.clone()))
            .collect();
        let releases = binding
            .releases
            .iter()
            .map(|r| schedule.release_recipe(&r.contents, &binding.entry, &captures))
            .collect::<Option<_>>()?;
        let returns = effects
            .protected_versions
            .returns
            .iter()
            .map(|out| {
                if out.origins.is_empty() {
                    return None;
                }
                schedule.recipe(&out.contents, Some(&binding.entry), &captures)
            })
            .collect::<Option<_>>()?;
        Some(Self {
            worker,
            access: schedule.position(&binding.entry)?.clone(),
            interval,
            binding,
            releases,
            returns,
        })
    }
}
