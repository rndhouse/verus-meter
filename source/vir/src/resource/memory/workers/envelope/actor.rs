//! Export byte bounds only from the source actor that can prove them.

use super::*;

/// Only immutable scalar inputs can be read outside the worker. A vector's
/// initial reservation is a candidate bound on its current charge. Each use
/// of that candidate is checked in the worker before it is exported.
fn export(
    value: &Expr,
    reservations: &HashMap<VarIdent, Expr>,
    captures: &HashMap<VarIdent, Expr>,
) -> Option<(Expr, Expr)> {
    let local = simplify::specialize(value, reservations);
    crate::resource::memory::synchronization::versions::operands(&local)?
        .iter()
        .all(|name| captures.contains_key(name))
        .then(|| (local.clone(), simplify::specialize(&local, captures)))
}

fn checked_cost(
    span: &Span,
    cost: &Footprint,
    reservations: &HashMap<VarIdent, Expr>,
    captures: &HashMap<VarIdent, Expr>,
    checks: &mut Vec<Obligation>,
    shared: Option<&Expr>,
) -> Option<Expr> {
    let value = cost.total();
    let (local, exported) = export(&value, reservations, captures).or_else(|| {
        // Price the unresolved portion of a shared observation together. The
        // history proposes a ceiling; the full original cost must prove it at
        // this exact site, including displaced elements and helper workspace.
        fn known(
            value: &Expr,
            reservations: &HashMap<VarIdent, Expr>,
            captures: &HashMap<VarIdent, Expr>,
        ) -> Expr {
            if let Some((local, _)) = export(value, reservations, captures) {
                return local;
            }
            if let ExprX::Binary(BinaryOp::Arith(ArithOp::Add(_)), a, b) = &value.x {
                return contracts::add(
                    &value.span,
                    known(a, reservations, captures),
                    known(b, reservations, captures),
                );
            }
            contracts::literal(&value.span, 0)
        }
        let proposal = contracts::add(span, known(&value, reservations, captures), shared?.clone());
        export(&proposal, reservations, captures)
    })?;
    if !simplify::inspect::same_expression(&value, &local) {
        checks.push(Obligation {
            contributor: None,
            span: span.clone(),
            cost: cost.clone(),
            bound: MemoryBudget::total(local),
            kind: CheckKind::WorkerState("at a worker phase"),
        });
    }
    Some(exported)
}

impl Execution {
    pub(super) fn phase_inputs(
        &self,
        analysis: &Analysis<'_>,
        parameters: &HashSet<VarIdent>,
        span: &Span,
    ) -> Option<HashMap<VarIdent, Expr>> {
        let mut captures = HashMap::new();
        for input in &self.inputs {
            if contracts::scalar(&input.typ) {
                let mut source = self.immutable_scalars.get(&input.name);
                let mut caller = self.publication.caller;
                while let Some(id) = caller {
                    let parent = &analysis.growth.worker_executions[&id];
                    // Nested capture metadata names the original lexical binding.
                    // Each intermediate closure must preserve that scalar.
                    source = source.filter(|name| {
                        parent.immutable_scalars.values().any(|actual| actual == *name)
                    });
                    caller = parent.publication.caller;
                }
                if let Some(name) = source.filter(|name| parameters.contains(*name)) {
                    captures.insert(
                        input.name.clone(),
                        SpannedTyped::new(span, &input.typ, ExprX::Var(name.clone())),
                    );
                }
            } else if !analysis.layouts.private_worker_buffer(&input.typ)
                && !analysis.layouts.inline_protocol_value(&input.typ)
                && !matches!(&*input.typ, TypX::Decorate(TypDecoration::Arc, _, item)
                if contracts::scalar(item) || analysis.layouts.inline_protocol_value(item) || analysis.layouts.mutex_payload(item).is_some_and(|t| analysis.layouts.plain_protected_payload(t)))
            {
                return None;
            }
        }
        Some(captures)
    }

    fn result_reservations(
        &self,
        analysis: &Analysis<'_>,
        allowed: &HashSet<VarIdent>,
        reservations: &mut HashMap<VarIdent, Expr>,
    ) -> Option<()> {
        // A checked result carries its own reservation across the call. Use
        // the actual scalar operands and the returned charge identities. A
        // proposal is still checked at every use, including after mutation.

        for (target, site) in &self.effects.calls {
            use crate::resource::memory::transfer::checked::Operation;
            let Some(Operation::Call { args, returned, budget, .. }) =
                self.effects.ownership.operation_at(site)
            else {
                return None;
            };
            if analysis.summaries[target].worker_parameter().is_some() {
                return None;
            }
            let function = &analysis.functions[target];
            let result = &function.x.outer_ret.x.typ;
            if !analysis.layouts.vector(result) || analysis.layouts.owning_elements(result) {
                continue;
            }
            let element = analysis.layouts.vector_element(result, site).ok()?;
            let amount = analysis.summaries[target]
                .vectors
                .returned_capacities
                .get(&Vec::new())
                .and_then(|capacity| contracts::substitute(capacity, function, args, allowed).ok())
                .map(|capacity| {
                    contracts::multiply(site, capacity, contracts::literal(site, element))
                })
                .unwrap_or_else(|| budget.clone());
            let ids: BTreeSet<_> = returned.iter().flat_map(|view| view.dynamic_ids()).collect();
            for vector in &analysis.growth.vectors {
                if ids.contains(&vector.backing.id)
                    && let ExprX::Var(name) = &vector.backing.bytes.x
                {
                    reservations.entry(name.clone()).or_insert_with(|| amount.clone());
                }
            }
        }
        Some(())
    }

    fn shared_proposal(
        &self,
        analysis: &Analysis<'_>,
        captures: &HashMap<VarIdent, Expr>,
        span: &Span,
    ) -> Option<Expr> {
        let mut local_parameters = HashMap::new();
        for (name, value) in captures {
            let ExprX::Var(formal) = &value.x else { return None };
            local_parameters.insert(
                formal.clone(),
                SpannedTyped::new(span, &value.typ, ExprX::Var(name.clone())),
            );
        }
        let mut shared = None;
        for root in self.versioned_roots().collect::<BTreeSet<_>>() {
            let bytes = analysis.transitions.protected_histories.get(&root)?.idle_bytes(span)?;
            let bytes = simplify::specialize(&bytes, &local_parameters);
            shared = Some(shared.map_or(bytes.clone(), |n| contracts::add(span, n, bytes)));
        }
        shared
    }

    pub(super) fn phases(
        &self,
        analysis: &Analysis<'_>,
        parameters: &HashSet<VarIdent>,
        reservations: &HashMap<VarIdent, Expr>,
        checks: &mut Vec<Obligation>,
        constraints: &mut Constraints,
        children: &[(WorkerId, Phases)],
    ) -> Option<Phases> {
        let span = &self.entry.definition.span;
        let initial = self.initial.live_expression(span).total();
        let completed = self.retained.live_expression(span).total();
        if contracts::constant(&initial).is_none()
            || !analysis.layouts.phase_result(&self.result.typ)
        {
            return None;
        }
        let captures = self.phase_inputs(analysis, parameters, span)?;
        let mut reservations = reservations.clone();
        self.result_reservations(analysis, &captures.keys().cloned().collect(), &mut reservations)?;
        let shared = self.shared_proposal(analysis, &captures, span);
        let native: BTreeSet<_> =
            self.effects.ownership.mutex_intervals(&analysis.transitions).collect();
        let mut phases = Phases::default();
        // Completion releases the working frame but retains the inline result
        // with its handle until join. Both entry and completion are unrestricted.
        phases.insert(Held::new(), initial);
        if contracts::constant(&completed).is_some() {
            phases.insert(Held::new(), completed);
        } else {
            if self.exits.is_empty() {
                return None;
            }
            for (exit, retained) in &self.exits {
                phases.insert(
                    Held::new(),
                    checked_cost(
                        exit,
                        retained,
                        &reservations,
                        &captures,
                        checks,
                        shared.as_ref(),
                    )?,
                );
            }
        }
        for p in self.effects.points.iter() {
            let exported =
                checked_cost(&p.span, &p.cost, &reservations, &captures, checks, shared.as_ref())?;
            let mut held: Held = p
                .condition
                .held
                .iter()
                .filter(|i| native.contains(i))
                .map(|i| (Class::Mutex(i.instance), 1))
                .collect();
            // A helper can release or transfer part of its incoming region at
            // an internal phase. Only directly observed ownership replaces
            // the cell's separate idle charge.
            if !self.effects.calls.iter().any(|(_, call)| call.id == p.span.id) {
                for interval in &p.payload_views {
                    if p.condition.held.contains(interval)
                        && let Some(root) =
                            self.effects.ownership.protected_versions.root_of(*interval)
                    {
                        held.insert(Class::Payload(root), 1);
                    }
                }
            }
            for witness in &p.holders {
                if let Some(role) = self.effects.ownership.holders.population_role(*witness) {
                    let class = constraints.register(analysis, parameters, span, role);
                    held.insert(class, 1);
                }
            }
            let mut local = Phases::default();
            local.insert(held, exported);
            for (_, child) in outstanding(p, children, &analysis.growth) {
                let keep =
                    local.0.keys().chain(child.0.keys()).flat_map(|h| h.keys().copied()).collect();
                local.include_peer(child, &keep, constraints, &p.span);
            }
            for (held, costs) in local.0 {
                for cost in costs {
                    phases.insert(held.clone(), cost);
                }
            }
        }
        Some(phases)
    }
}
