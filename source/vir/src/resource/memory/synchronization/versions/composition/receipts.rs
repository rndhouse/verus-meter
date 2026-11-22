//! Fixed acquisitions share a release order across observations. Repeated
//! acquisitions admit any contents preserved by every executable release.
use super::*;

/// Every index denotes an alternative. Out-of-range indices select the first.
fn choose(site: &Span, index: &Expr, values: impl Iterator<Item = Expr>) -> Option<Expr> {
    use crate::resource::memory::transfer::simplify::inspect::same_expression;
    let mut values = values.enumerate();
    let (_, first) = values.next()?;
    let mut other: Vec<(Expr, Vec<Expr>)> = Vec::new();
    for (i, value) in values {
        // Keep the shared history index even when different release orders
        // produce identical bytes here. Only the proof of this projection is shared.
        if same_expression(&value, &first) {
            continue;
        }
        let condition = mk_eq(site, index, &expr::integer(site, i as i128));
        if let Some((_, indices)) = other.iter_mut().find(|(v, _)| same_expression(v, &value)) {
            indices.push(condition);
        } else {
            other.push((value, vec![condition]));
        }
    }
    let typ = first.typ.clone();
    Some(other.into_iter().fold(first, |previous, (value, indices)| {
        let condition = crate::ast_util::disjoin(site, &indices);
        SpannedTyped::new(site, &typ, ExprX::If(condition, value, Some(previous)))
    }))
}

impl Evidence {
    fn choice_index(&mut self, site: &Span, name: &str) -> Expr {
        let int = crate::ast_util::int_typ();
        let (index, decl) = expr::local(
            site,
            name,
            int.clone(),
            SpannedTyped::new(site, &int, ExprX::Nondeterministic),
            Mode::Spec,
        );
        self.declarations.push((site.id, decl));
        index
    }

    pub(super) fn joined_outcomes(
        &mut self,
        function: &Function,
        history: &History,
        sections: &[Section<'_>],
        observations: &[Observation],
    ) -> Option<()> {
        let body = function.x.body.as_ref()?;
        let history_index =
            (!history.repeated).then(|| self.choice_index(&body.span, "mutex_history"));
        for observation in observations {
            let snapshot = &observation.snapshot;
            let site = &snapshot.span;
            let returning = match observation.result {
                Some(actor) => Some(
                    sections.iter().find(|s| s.worker.actor == actor && !s.returns.is_empty())?,
                ),
                None => None,
            };
            let empty = expr::empty(site, expr::record_type());
            let exit_index = self.choice_index(site, "worker_exit");
            let mut choices = Vec::new();
            if history.repeated {
                // Induction forgets order. Each observation makes its own
                // choice; sharing an index could tie two independent visits.
                let mut states = history.candidates();
                if let Some(section) = returning {
                    states.push(&empty);
                    for input in states {
                        choices.extend(
                            section
                                .returns
                                .iter()
                                .map(|r| r.apply(Some((&section.binding.entry, input)))),
                        );
                    }
                } else {
                    choices.extend(states.into_iter().cloned());
                }
            } else {
                for state in history.terminal_states() {
                    let value = if let Some(section) = returning {
                        let input = history.input_before(state, section.interval).unwrap_or(&empty);
                        choose(
                            site,
                            &exit_index,
                            section
                                .returns
                                .iter()
                                .map(|recipe| recipe.apply(Some((&section.binding.entry, input)))),
                        )?
                    } else {
                        choose(
                            site,
                            &exit_index,
                            history.at_join(state, observation).into_iter().cloned(),
                        )?
                    };
                    choices.push(value);
                }
            }
            let selector = history_index.as_ref().unwrap_or(&exit_index);
            let value = choose(site, selector, choices.into_iter())?;
            let mut facts = Vec::new();
            crate::resource::memory::transfer::prove_forest(site, &value, &mut facts).ok()?;
            self.snapshots.push((snapshot.clone(), Some(value), facts));
        }
        Some(())
    }
}
