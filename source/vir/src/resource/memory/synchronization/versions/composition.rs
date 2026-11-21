//! Compose finite critical sections from the same canonical mutex. Every
//! specialization has a base obligation at publication and a step obligation
//! at the executable release. Join order supplies neither premise.

mod receipts;

use super::{
    history::Section,
    recipe::{Schedule, assignment, variable},
    *,
};
use crate::ast_util::{bool_typ, mk_eq, mk_implies};
use crate::resource::memory::{
    growth::Growth,
    workers::{WorkerId, execution::Execution},
};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

impl Growth {
    /// Insert evidence immediately at the assignment that freezes the value.
    /// A missing or ambiguous site cannot establish a transition.
    fn at_snapshot(
        &mut self,
        snapshot: &Expr,
        replace: Option<Expr>,
        checks: Vec<Stmt>,
    ) -> Result<(), VirErr> {
        let name = variable(snapshot);
        let site = snapshot.span.id;
        let mut found = false;
        for schedule in
            [&mut self.before, &mut self.updates, &mut self.after, &mut self.operand_observations]
        {
            let Some(actions) = schedule.get_mut(&site) else { continue };
            let mut matches = actions.iter().enumerate().filter_map(|(i, action)| {
                assignment(action).is_some_and(|(n, _)| n == name).then_some(i)
            });
            let Some(index) = matches.next() else { continue };
            if found || matches.next().is_some() {
                return Err(unsupported(
                    &snapshot.span,
                    "multiple definitions of a shared payload snapshot",
                ));
            }
            found = true;
            if let Some(value) = &replace {
                actions[index] = expr::assign(&snapshot.span, snapshot, value.clone());
            }
            actions.splice(index + 1..index + 1, checks.iter().cloned());
        }
        if !found {
            return Err(unsupported(
                &snapshot.span,
                "a shared payload snapshot without its defining operation",
            ));
        }
        Ok(())
    }
}

impl Analysis<'_> {
    pub(in crate::resource::memory) fn observe_payload_seeds(
        &mut self,
        actor: WorkerId,
        span: &Span,
    ) {
        if self.current_worker.is_some() || !self.growth.worker_occurrences[&actor].is_empty() {
            return;
        }
        let worker = self.growth.worker_executions[&actor].clone();
        for root in worker.versioned_roots().collect::<BTreeSet<_>>() {
            let Some(payload) = self
                .heap
                .shared
                .payload(root)
                .and_then(|mutex| mutex.children.get(&OwnerSlot::Contents))
                .cloned()
            else {
                continue;
            };
            self.heap.shared.publish_payload_holder(root, actor);
            if !complete_contents(&payload) {
                continue;
            }
            // The spawn operands can construct or change the backing. Snapshot
            // the publisher's canonical forest after those operands, just as
            // for the ordinary capture publication.
            let start = self.growth.before.get(&span.id).map_or(0, Vec::len);
            let seed = self.snapshot_owner_metadata(span, &payload);
            let observations = self.growth.before.entry(span.id).or_default().split_off(start);
            self.growth.after.entry(span.id).or_default().extend(observations);
            let origins = self.storage.returned_storage(Some(&payload), &self.growth.elements);
            self.growth
                .protected_seeds
                .insert((actor, root), Publication { contents: seed, origins });
        }
    }

    pub(in crate::resource::memory) fn compose_payload_versions(
        &mut self,
        function: &Function,
    ) -> Result<usize, VirErr> {
        if self.growth.protected_seeds.is_empty() && self.growth.protected_observations.is_empty() {
            return Ok(0);
        }
        let mut groups = BTreeMap::<RootId, Vec<(Arc<Execution>, Interval)>>::new();
        for worker in self.growth.worker_executions.values() {
            for (&interval, binding) in &worker.effects.ownership.protected_versions.bindings {
                groups.entry(binding.root).or_default().push((worker.clone(), interval));
            }
        }
        // Every protected borrow must participate. A helper or exclusive
        // worker without an imported release relation cannot silently count
        // as a reader. Parent mutations need their own ordered summary.
        let mut unlinked = self.transitions.payload_borrows();
        for worker in self.growth.worker_executions.values() {
            let effects = &worker.effects.ownership;
            unlinked.extend(
                effects
                    .payload_borrows()
                    .into_iter()
                    .filter(|interval| !effects.protected_versions.bindings.contains_key(interval)),
            );
        }
        let unlinked: BTreeSet<_> = unlinked.iter().map(|id| id.instance).collect();
        let publisher = Schedule::for_body(
            &self.growth,
            function.x.body.as_ref().expect("analyzed function body"),
        );
        let mut plans = Vec::new();
        for (root, members) in groups {
            if !unlinked.contains(&members[0].1.instance)
                && let Some((history, proof)) =
                    plan(&self.growth, &publisher, function, root, &members)
            {
                plans.push((root, history, proof));
            }
        }
        for (root, observations) in &self.growth.protected_observations {
            if observations.iter().any(|o| o.result.is_some())
                && !plans.iter().any(|(linked, _, _)| linked == root)
            {
                return Err(unsupported(
                    &observations[0].snapshot.span,
                    "a joined outcome without a complete checked history for its mutex",
                ));
            }
        }
        for (root, history, proof) in plans {
            for (site, declaration) in proof.declarations {
                self.growth.before.entry(site).or_default().insert(0, declaration);
            }
            for (snapshot, replacement, checks) in proof.snapshots {
                self.growth.at_snapshot(&snapshot, replacement, checks)?;
            }
            self.transitions.protected_histories.insert(root, history);
        }
        Ok(self.transitions.protected_histories.values().map(History::acquisitions).sum())
    }
}

/// Keep the unrestricted input if a source value is opaque, an acquisition
/// repeats, or the number of finite alternatives is too expensive to expand.
/// Discard the whole root's proposal before changing any worker.
#[derive(Default)]
struct Evidence {
    /// Erased scalar inputs in the worker proof scope.
    declarations: Vec<(AstId, Stmt)>,
    /// Each substitution or check is installed at its defining operation.
    snapshots: Vec<(Expr, Option<Expr>, Vec<Stmt>)>,
}

fn plan(
    growth: &Growth,
    publisher: &Schedule<'_>,
    function: &Function,
    root: RootId,
    members: &[(Arc<Execution>, Interval)],
) -> Option<(History, Evidence)> {
    let mut seeds = Vec::new();
    let mut proof = Evidence::default();
    let parameters: HashMap<_, _> = crate::resource::memory::contracts::inputs(function)
        .into_iter()
        .map(|n| (n.clone(), n))
        .collect();
    let mut used = BTreeSet::new();
    let mut sections = Vec::new();
    for (worker, interval) in members {
        let effects = &worker.effects.ownership;
        let binding = &effects.protected_versions.bindings[interval];
        if !effects.fixed_acquisition(*interval)
            || !binding.access.single_visit()
            || !binding.releases.iter().all(|r| r.complete && r.visit.single_visit())
        {
            return None;
        }
        let seed = growth.protected_seeds.get(&(worker.actor, root))?;
        if seed.origins.is_empty() {
            return None;
        }
        let recipe = publisher.recipe(&seed.contents, None, &parameters)?;
        used.extend(recipe.parameters.iter().cloned());
        let initial = recipe.apply(None);
        seeds.push((seed.clone(), initial));
        let schedule = Schedule::for_body(growth, &worker.effects.body);
        let captures = worker
            .immutable_scalars
            .iter()
            .filter(|(_, n)| parameters.contains_key(*n))
            .map(|(local, formal)| (local.clone(), formal.clone()))
            .collect();
        let releases: Vec<super::recipe::Recipe> = binding
            .releases
            .iter()
            .map(|r| schedule.release_recipe(&r.contents, &binding.entry, &captures))
            .collect::<Option<_>>()?;
        used.extend(releases.iter().flat_map(|r| r.parameters.iter().cloned()));
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
            .collect::<Option<Vec<_>>>()?;
        used.extend(returns.iter().flat_map(|r| r.parameters.iter().cloned()));
        sections.push(Section {
            worker,
            access: schedule.position(&binding.entry)?.clone(),
            interval: *interval,
            binding,
            releases,
            returns,
        });
    }
    let history = History::build(seeds, &sections)?;
    if let Some(observations) = growth.protected_observations.get(&root) {
        proof.joined_outcomes(function, &history, &sections, observations)?;
    }
    for (publication, initial) in history.seeds() {
        let snapshot = &publication.contents;
        let check = expr::check(
            &snapshot.span,
            mk_eq(&snapshot.span, snapshot, initial),
            "initial shared payload differs from its publication descriptor",
        );
        proof.snapshots.push((snapshot.clone(), None, vec![check]));
    }
    for section in sections {
        let input = &section.binding.entry;
        let site = &input.span;
        // Immutable publisher inputs denote the same values throughout the
        // history. A worker with no capture must prove its part for every
        // value of that Rust type. Its proof cannot read a publisher local.
        let mut bindings = HashMap::new();
        for parameter in function.x.params.iter().filter(|p| used.contains(&p.x.name)) {
            let typ = &parameter.x.typ;
            let initial = section
                .worker
                .captured_parameter(&parameter.x.name, typ)
                .unwrap_or_else(|| SpannedTyped::new(site, typ, ExprX::Nondeterministic));
            let (local, decl) =
                expr::local(site, "payload_parameter", typ.clone(), initial, Mode::Spec);
            proof.declarations.push((section.worker.effects.body.span.id, decl));
            bindings.insert(parameter.x.name.clone(), local);
        }
        let bind = |term: &Expr| {
            if bindings.is_empty() {
                term.clone()
            } else {
                crate::resource::memory::transfer::simplify::specialize(term, &bindings)
            }
        };
        let states: Vec<_> = history.inputs(section.interval).into_iter().map(bind).collect();
        let empty = expr::empty(site, expr::record_type());
        for (exit, recipe) in
            section.worker.effects.ownership.protected_versions.returns.iter().zip(&section.returns)
        {
            let origin = &exit.contents;
            let site = &origin.span;
            let mut checks = Vec::new();
            for state in history.inputs(section.interval).into_iter().chain(std::iter::once(&empty))
            {
                let result = recipe.apply(Some((input, state)));
                recipe.result_facts(site, input, &bind(state), &bindings, &mut checks)?;
                checks.push(expr::check(
                    site,
                    mk_implies(
                        site,
                        &mk_eq(site, input, &bind(state)),
                        &mk_eq(site, origin, &bind(&result)),
                    ),
                    "completed worker result differs from its checked exit",
                ));
            }
            proof.snapshots.push((origin.clone(), None, checks));
        }
        let mut options = states.iter();
        let mut choice = options.next()?.clone();
        for state in options {
            let either = SpannedTyped::new(site, &bool_typ(), ExprX::Nondeterministic);
            choice =
                SpannedTyped::new(site, &input.typ, ExprX::If(either, state.clone(), Some(choice)));
        }
        for release in &section.binding.releases {
            let output = &release.contents;
            let site = &output.span;
            let mut checks = Vec::new();
            for (state, next) in history.transitions(section.interval, output) {
                let condition = mk_implies(
                    site,
                    &mk_eq(site, input, &bind(state)),
                    &mk_eq(site, output, &bind(next)),
                );
                checks.push(expr::check(
                    site,
                    condition,
                    "released shared payload differs from its checked transition",
                ));
            }
            proof.snapshots.push((output.clone(), None, checks));
        }
        let mut facts = Vec::new();
        for state in &states {
            crate::resource::memory::transfer::prove_forest(site, state, &mut facts).ok()?;
        }
        proof.snapshots.push((input.clone(), Some(choice), facts));
    }
    Some((history, proof))
}
