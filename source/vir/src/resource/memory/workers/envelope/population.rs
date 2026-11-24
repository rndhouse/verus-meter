//! A collected family has one outstanding occurrence per published, unjoined
//! handle. Completion can move an occurrence to its zero-scratch state before
//! join. Until collection its tag stays charged in the caller's ownership tree.
//!
//! Initially every phase is empty. Spawn adds one occurrence at entry. A wait,
//! acquisition, release or completion moves that same occurrence between its
//! checked phases, preserving their sum. Join removes one completed occurrence.
//! These moves take an existing member, so no phase becomes negative, and two
//! members cannot hold the same mutex. Only the sum needs an erased counter.

mod observations;

use super::*;
use crate::ast_util::{mk_eq, mk_ineq};
use crate::resource::memory::{growth::select, metadata::expr};

/// Distribute the population over additive workspace (e.g. n*b + n*24).
/// Keep multiplication in mathematical integers, as in loop byte proofs.
fn scale(span: &Span, count: &Expr, cost: &Expr) -> Expr {
    match &cost.x {
        ExprX::Binary(BinaryOp::Arith(ArithOp::Add(_)), a, b) => {
            contracts::add(span, scale(span, count, a), scale(span, count, b))
        }
        ExprX::If(condition, a, Some(b)) => {
            select(span, condition.clone(), scale(span, count, a), scale(span, count, b))
        }
        _ => contracts::multiply(span, count.clone(), cost.clone()),
    }
}

impl Phases {
    /// Partition the occurrences by one held mutex, or by the unrestricted
    /// state (including completion). Their counts sum to the outstanding
    /// population. Mutual exclusion limits each assigned mutex class to one.
    /// A phase holding several locks can safely use any one of them.
    fn population_peak(&self, span: &Span, count: &Expr) -> Expr {
        let free = &self.0[&BTreeSet::new()];
        let baseline = maximum_cost(span, free);
        let mut groups = BTreeMap::<Instance, Vec<Expr>>::new();
        for (held, costs) in &self.0 {
            if let Some(&instance) = held.first() {
                groups.entry(instance).or_default().extend(costs.iter().cloned());
            }
        }
        let unrestricted = scale(span, count, &baseline);
        if groups.is_empty() {
            return unrestricted;
        }
        let zero = contracts::literal(span, 0);
        let mut exclusive = unrestricted;
        for group in groups.values() {
            let guarded = maximum_cost(span, group);
            let excess = contracts::subtract(span, guarded, baseline.clone());
            exclusive =
                contracts::add(span, exclusive, contracts::maximum(span, zero.clone(), excess));
        }
        // Small populations cannot fill all the mutex classes. The independent
        // bound also yields exactly zero when no occurrence has been published.
        let all = scale(span, count, &self.peak(span).unwrap());
        contracts::minimum(span, exclusive, all)
    }
}

impl Analysis<'_> {
    pub(super) fn compose_population(
        &mut self,
        function: &Function,
        workers: BTreeMap<WorkerId, Phases>,
        checks: Vec<Obligation>,
    ) -> bool {
        // One homogeneous family. A selected join must consume precisely one
        // member. Mixed families need their own counted membership relation.
        if workers.len() != 1 {
            return false;
        }
        let (id, phases) = workers.into_iter().next().unwrap();
        let [(head, _)] = self.growth.worker_occurrences[&id].as_slice() else { return false };
        let Some(control) = self.transitions.loops.get(head).and_then(|r| r.control.as_ref())
        else {
            return false;
        };
        let span = &function.span;
        let upper = match control.comparison {
            InequalityOp::Lt | InequalityOp::Le => &control.end,
            InequalityOp::Gt | InequalityOp::Ge => &control.start,
        };
        let Ok(mut limit) = contracts::quantity(upper, &contracts::inputs(function)) else {
            return false;
        };
        if matches!(control.comparison, InequalityOp::Le | InequalityOp::Ge) {
            limit = contracts::add(span, limit, contracts::literal(span, 1));
        }
        let body = function.x.body.as_ref().unwrap();
        let spawn = self.growth.worker_executions[&id].publication.span.clone();
        let pending = self.prove_outstanding_count(span, &body.span, &spawn, &limit);
        // Use the checked immutable ceiling for observations attached to
        // an expression containing spawn or join. Its operands can change the
        // live population before the observed Rust storage reaches its peak.
        let envelope = phases.population_peak(span, &limit);
        let actual = phases.population_peak(span, &pending);
        // Both expressions bound the same population. Keeping the known
        // ceiling also lets ordinary arithmetic use a declared n*b directly.
        let bounded = contracts::minimum(span, actual, envelope.clone());
        let stable = observations::stable_sites(body, spawn.id, &self.growth.worker_joins);
        let additions = self
            .storage
            .points()
            .iter()
            .map(|p| {
                Some(if stable.contains(&p.span.id) { bounded.clone() } else { envelope.clone() })
            })
            .collect();
        self.storage.include_worker_costs(additions);
        self.obligations.extend(checks);
        true
    }

    /// The shadow count starts at zero, advances on a checked publication and
    /// falls only on a normal join. Its loop and exit equalities are VCs.
    fn prove_outstanding_count(
        &mut self,
        span: &Span,
        body: &Span,
        spawn: &Span,
        limit: &Expr,
    ) -> Expr {
        let zero = contracts::literal(span, 0);
        let one = contracts::literal(span, 1);
        let (pending, declaration) = expr::local(
            span,
            "outstanding_workers",
            crate::ast_util::int_typ(),
            zero.clone(),
            Mode::Spec,
        );
        self.growth.declarations.push(declaration);
        for record in self.transitions.loops.values() {
            // Candidate equality only. Verus must prove that the actual handle
            // vector lengths account for every outstanding occurrence at this
            // head, initially and on every back edge.
            let mut slots = zero.clone();
            for (typ, forest) in record.reference_forests.values() {
                if self.collection_worker_payload(typ).is_some()
                    && let Some(length) = record.forest_length(forest)
                {
                    slots = contracts::add(span, slots, length.clone());
                }
            }
            self.growth.loops.entry(record.span.id).or_default().extend([
                mk_eq(&record.span, &pending, &slots),
                mk_ineq(&record.span, &zero, &pending, InequalityOp::Le),
                mk_ineq(&record.span, &pending, limit, InequalityOp::Le),
            ]);
        }
        let next = contracts::add(spawn, pending.clone(), one.clone());
        self.growth.after.entry(spawn.id).or_default().extend([
            expr::check(
                spawn,
                mk_ineq(spawn, &next, limit, InequalityOp::Le),
                "cannot prove the outstanding worker population fits its loop bound",
            ),
            expr::assign(spawn, &pending, next),
        ]);
        for &join in self.growth.worker_joins.keys() {
            let remaining = contracts::subtract(span, pending.clone(), one.clone());
            self.growth.after.entry(join).or_default().extend([
                expr::check(
                    span,
                    mk_ineq(span, &zero, &remaining, InequalityOp::Le),
                    "worker join requires an outstanding publication",
                ),
                expr::assign(span, &pending, remaining),
            ]);
        }
        for exit in self
            .transitions
            .exits
            .iter()
            .filter_map(|(id, target)| {
                matches!(target, crate::resource::memory::control::Target::Return).then_some(*id)
            })
            .chain([body.id])
        {
            self.growth.after.entry(exit).or_default().push(expr::check(
                span,
                mk_eq(span, &pending, &zero),
                "outstanding workers at the end of a closed memory contract",
            ));
        }
        pending
    }
}
