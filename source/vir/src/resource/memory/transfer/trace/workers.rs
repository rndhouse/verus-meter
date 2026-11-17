//! Worker transport uses the same checked capture and ownership templates as
//! body accounting. Snapshot data is immutable across repeated constructions.

use super::*;
use crate::resource::memory::concurrency::CaptureMode;

impl Trace<'_> {
    pub(super) fn closure(
        &mut self,
        value: &Expr,
        captures: Vec<(CaptureMode, checked::Place)>,
    ) -> Option<Value> {
        let span = &value.span;
        let mut memory = expr::empty(span, expr::record_type());
        for (index, (mode, capture)) in captures.into_iter().enumerate() {
            let path = expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Capture(index))]);
            if contracts::scalar(&capture.typ) {
                let scalar = self.scalar(&capture.source)?;
                memory = expr::push(span, memory, expr::scalar_observation(span, path, scalar));
            } else if self.layouts.owner(&capture.typ) {
                if mode != CaptureMode::Move {
                    return None;
                }
                let location = self.checked_location(&capture)?;
                let owner = self.take(span, &location, &capture.typ)?;
                if self.checked.moves.contains_key(&capture.source.span.id) {
                    self.used.insert((checked::Kind::Move, capture.source.span.id));
                }
                memory = expr::add(span, memory, expr::prefix(span, owner.memory, path));
            } else {
                return None;
            }
        }
        Some(Value::Owner(Node {
            origin: None,
            typ: value.typ.clone(),
            memory,
            minima: Default::default(),
        }))
    }

    pub(super) fn publish_worker(
        &mut self,
        value: &Expr,
        source: Expr,
        identity: Expr,
        inputs: Vec<(Typ, OwnerSlot)>,
        populations: HashMap<usize, Expr>,
        template: Template,
    ) -> Option<Value> {
        let span = &value.span;
        let Value::Owner(captures) = self.value(&source)? else { return None };
        let selected = |index: usize, path: &[OwnerSlot]| {
            let slots = std::iter::once(&inputs[index].1)
                .chain(path.iter())
                .map(|slot| self.layouts.metadata_slot(slot));
            simplify::simplify(&expr::subtree(
                span,
                captures.memory.clone(),
                expr::path(span, slots),
            ))
        };
        // A publishing trace knows the collection built by the source, including
        // each indexed result. The receiving actor checks this candidate against
        // its actual collection at loop entry and at every back edge.
        if !populations.is_empty() && self.loop_tokens.is_none() {
            // Only source scalar parameters and expression-local binders are
            // in scope at every construction. An open candidate keeps the
            // worker's checked entry snapshot as its proof input.
            let parameters: HashSet<_> = self
                .symbols
                .iter()
                .filter_map(|s| {
                    if matches!(s.input, Input::Scalar(_))
                        && let ExprX::Var(name) = &self.proof_values.get(&s.name)?.x
                    {
                        Some(name)
                    } else {
                        None
                    }
                })
                .collect();
            for (index, snapshot) in populations {
                let ExprX::Var(name) = &snapshot.x else { return None };
                let memory = substitute(&selected(index, &[]), &self.proof_values);
                let closed = crate::ast_visitor::expr_visitor_check(&memory, &mut |scope, e| {
                    if let ExprX::Var(var) = &e.x
                        && !scope.contains_key(var)
                        && !parameters.contains(var)
                    {
                        return Err(());
                    }
                    Ok(())
                });
                if closed.is_ok() {
                    self.publications.insert(name.clone(), memory);
                }
            }
        }
        let mut replacements = HashMap::new();
        for symbol in &template.symbols {
            let replacement = match &symbol.input {
                Input::Complete => crate::ast_util::mk_bool(span, true),
                Input::Forest(index) => selected(*index, &[]),
                Input::Scalar(index) => {
                    expr::observed_scalar(span, selected(*index, &[]), &inputs[*index].0)?
                }
                Input::Property(index, path, field) => {
                    property(span, selected(*index, path), field)
                }
                Input::Minimum(_, _) => expr::integer(span, 0),
            };
            replacements.insert(symbol.name.clone(), replacement);
        }
        let result = instantiate_value(&template.result, &replacements);
        if matches!(result, Value::Iterator(_)) {
            return None;
        }
        let result = worker_description(span, result)
            .map_or_else(|| expr::empty(span, expr::record_type()), |node| node.memory);
        // Progress inference already relates each erased ordinal to the bound
        // visit index. Reuse that relation; a compiler visit is not a count.
        let indices = self
            .proof_values
            .iter()
            .filter_map(|(name, observation)| {
                if let ExprX::Var(observed) = &observation.x {
                    Some((
                        observed.clone(),
                        SpannedTyped::new(span, &observation.typ, ExprX::Var(name.clone())),
                    ))
                } else {
                    None
                }
            })
            .collect();
        let identity = substitute(&identity, &indices);
        let record = expr::operation(
            span,
            "worker_observation",
            vec![expr::path(span, []), identity, captures.memory, result],
            expr::record_type(),
        );
        let memory = expr::push(span, expr::empty(span, expr::record_type()), record);
        let tag = expr::operation(
            span,
            "allocated",
            vec![
                expr::path(span, [-1]),
                expr::integer(span, 0),
                contracts::literal(span, verus_meter_model::completion_bytes(0)?),
                expr::integer(span, 0),
                expr::integer(span, 0),
            ],
            expr::record_type(),
        );
        let memory = expr::push(span, memory, tag);
        Some(Value::Owner(Node {
            origin: None,
            typ: value.typ.clone(),
            memory,
            minima: Default::default(),
        }))
    }

    pub(super) fn join_worker(&mut self, value: &Expr, source: Expr) -> Option<Value> {
        let Value::Owner(handle) = self.value(&source)? else { return None };
        let span = &value.span;
        let record = expr::lookup(span, handle.memory, expr::path(span, []));
        let result = expr::operation(span, "worker_result", vec![record], expr::memory_type());
        let result = expr::prefix(
            span,
            result,
            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
        );
        let root =
            allocated(span, expr::integer(span, 0), expr::integer(span, 0), expr::integer(span, 1));
        let memory =
            expr::add(span, expr::push(span, expr::empty(span, expr::record_type()), root), result);
        Some(Value::Owner(Node {
            origin: None,
            typ: value.typ.clone(),
            memory,
            minima: Default::default(),
        }))
    }
}
