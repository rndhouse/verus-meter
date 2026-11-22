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
    /// This source lock can run on multiple visits to an enclosing loop.
    pub(super) repeated: bool,
    /// Immutable source guards to preserve in isolated loop queries.
    pub(super) loop_guards: Vec<(crate::messages::AstId, crate::ast::Expr)>,
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
    /// A lock visit owns its access and releases. Each release must describe the
    /// complete protected contents using the entry and immutable captures.
    pub(super) fn from_worker(
        growth: &Growth,
        worker: &'a Execution,
        interval: Interval,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Option<Self> {
        let effects = &worker.effects.ownership;
        let binding = &effects.protected_versions.bindings[&interval];
        let acquisition = effects.acquisition_visit(interval)?;
        if !acquisition.same_visit_scope(&binding.access)
            || !binding
                .releases
                .iter()
                .all(|r| r.complete && acquisition.same_visit_scope(&r.visit))
        {
            return None;
        }
        let schedule = Schedule::for_body(growth, &worker.effects.body);
        let captures: HashMap<_, _> = worker
            .immutable_scalars
            .iter()
            .filter(|(_, n)| parameters.contains_key(*n))
            .map(|(local, formal)| (local.clone(), formal.clone()))
            .collect();
        let local_parameters = captures.keys().map(|n| (n.clone(), n.clone())).collect();
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
            repeated: !acquisition.single_visit(),
            loop_guards: acquisition
                .loops()
                .flat_map(|site| {
                    schedule
                        .entry_guards(site, &local_parameters)
                        .into_iter()
                        .map(move |guard| (site, guard))
                })
                .collect(),
            worker,
            access: schedule.position(&binding.entry)?.clone(),
            interval,
            binding,
            releases,
            returns,
        })
    }
}
