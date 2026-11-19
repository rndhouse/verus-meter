//! Close an overwrite that depends only on inputs and the current visit.
//! Forget every overwritten input before tracing one visit. This prevents
//! first-visit coincidences from becoming recurrence or alias assumptions.

use super::*;

impl Trace<'_> {
    pub(super) fn overwritten_observations(&mut self, record: &Loop) -> Option<Value> {
        let control = record.control.as_ref()?;
        record.progress.as_ref()?;
        if record.nested || !record.conditional || !record.head_breaks.is_empty() {
            return None;
        }
        // The final false test must have no side effects. Other condition
        // forms retain the ordinary conservative loop fallback.
        for operand in [&control.start, &control.end] {
            if !matches!(operand.x, ExprX::Const(_))
                && crate::resource::memory::loops::local(operand).is_none()
            {
                return None;
            }
        }
        let entry = self.state.clone();
        let mut overwritten = Vec::new();
        for name in record.writes().filter(|name| !record.scalar_steps.contains_key(*name)) {
            if let Some(initial) = self.state.values.remove(name) {
                overwritten.push((name, initial));
            }
        }
        let span = &record.span;
        let binder = VarIdent(
            Arc::new("$memory_observation_visit".into()),
            VarIdentDisambiguate::VirTemp(span.id),
        );
        let progress = self.begin_progress(record, binder.clone())?;
        self.iteration(record)?;
        let (count, stride) = self.finish_progress(record, &progress)?;
        let mut facts = Vec::new();
        let mut results = Vec::new();
        for (name, initial) in overwritten {
            let local =
                SpannedTyped::new(span, record.written_type(name)?, ExprX::Var(name.clone()));
            let next = self.state.values.get(name)?;
            let (current, initial, next, slice) = match (initial, next) {
                (Value::Scalar(initial), Value::Scalar(next)) => (local, initial, next, false),
                (Value::CollectionLength(initial), Value::CollectionLength(next)) => (
                    crate::resource::memory::iterators::slice_length(span, local)?,
                    initial,
                    next,
                    true,
                ),
                _ => return None,
            };
            // At head k > 0 the last write was made on visit k - 1.
            let after = |k: &Expr| {
                let previous = contracts::subtract(span, k.clone(), expr::integer(span, 1));
                let last = substitute(next, &HashMap::from([(binder.clone(), previous)]));
                choice(span, mk_eq(span, k, &expr::integer(span, 0)), initial.clone(), last)
            };
            let closed = after(&count);
            let head = after(&SpannedTyped::new(span, &int_typ(), ExprX::Var(binder.clone())));
            crate::ast_visitor::expr_visitor_check(&head, &mut |scope, value| {
                if let ExprX::Var(name) = &value.x
                    && !scope.contains_key(name)
                    && !self.proof_values.contains_key(name)
                {
                    return Err(());
                }
                Ok(())
            })
            .ok()?;
            facts.push(mk_eq(span, &current, &substitute(&head, &self.proof_values)));
            results.push((
                name.clone(),
                if slice { Value::CollectionLength(closed) } else { Value::Scalar(closed) },
            ));
        }
        self.record_progress(record, &progress, stride, &[]);
        self.loop_progress.get_mut(&span.id)?.overwrites = facts;
        self.state = entry;
        self.complete_progress(record, &progress, &count);
        self.state.values.extend(results);
        self.used.insert((checked::Kind::Loop, span.id));
        Some(Value::Unit)
    }
}
