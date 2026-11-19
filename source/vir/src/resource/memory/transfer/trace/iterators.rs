//! Specialize checked iterator operations and their finite progress.
//!
//! Only the successful body of an accepted for record may advance symbolically.
//! The real next call and exhaustion edge remain subject to ordinary Verus proof.

use super::*;
use crate::resource::memory::{
    iterators::{Items, Operation, Sequence},
    loops::Loop,
};

impl Trace<'_> {
    pub(super) fn iterator_operation(
        &mut self,
        value: &Expr,
        operation: Operation,
    ) -> Option<Value> {
        let span = &value.span;
        let sequence = match operation {
            Operation::Range { fields } => {
                // A struct literal may spell end before start. Its field
                // initializers can call helpers that mutate heap ownership.
                let mut bounds = HashMap::new();
                for field in fields.iter() {
                    bounds.insert(field.name.as_str(), self.scalar(&field.a)?);
                }
                let first = bounds.remove("start")?;
                let end = bounds.remove("end")?;
                let count = contracts::maximum(
                    span,
                    expr::integer(span, 0),
                    contracts::subtract(span, end, first.clone()),
                );
                Sequence {
                    items: Items::Range { first, step: 1 },
                    count,
                    position: expr::integer(span, 0),
                }
            }
            Operation::BorrowCollection { source, vector } => {
                let count = if let Some(vector) = vector {
                    let location = self.checked_location(&vector)?;
                    if location.1.is_empty()
                        && let Some(Value::CollectionLength(length)) =
                            self.state.values.get(&location.0)
                    {
                        length.clone()
                    } else {
                        let owner = self.get(span, &location, &vector.typ)?;
                        self.effects.push(Effect::Read(location.0));
                        property(span, owner.memory, "length")
                    }
                } else {
                    let Value::CollectionLength(length) = self.value(&source)? else { return None };
                    length
                };
                Sequence { items: Items::Shared, count, position: expr::integer(span, 0) }
            }
            Operation::Adapt { kind, args } => {
                let Value::Iterator(mut source) = self.value(&args[0])? else { return None };
                use ResourceIntrinsic::*;
                match kind {
                    IteratorInto | IteratorWrap => {}
                    IteratorRev => {
                        let Items::Range { first, step } = &mut source.items else { return None };
                        *first = contracts::add(
                            span,
                            first.clone(),
                            contracts::multiply(
                                span,
                                expr::integer(span, *step),
                                contracts::subtract(
                                    span,
                                    source.count.clone(),
                                    expr::integer(span, 1),
                                ),
                            ),
                        );
                        *step = -*step;
                    }
                    IteratorTake | IteratorSkip => {
                        let amount = self.scalar(&args[1])?;
                        let selected = contracts::minimum(span, source.count.clone(), amount);
                        if kind == IteratorTake {
                            source.count = selected;
                        } else {
                            let Items::Range { first, step } = &mut source.items else {
                                return None;
                            };
                            *first = contracts::add(
                                span,
                                first.clone(),
                                contracts::multiply(
                                    span,
                                    expr::integer(span, *step),
                                    selected.clone(),
                                ),
                            );
                            source.count = contracts::subtract(span, source.count, selected);
                        }
                    }
                    _ => return None,
                }
                source
            }
            Operation::Advance { receiver } => {
                if self.active_iterator.as_ref() != Some(&receiver) {
                    return None;
                }
                // No source operation can manufacture this advance: the checked
                // record validated the actual wrapper type and next destination.
                let Value::Iterator(sequence) = self.state.values.get_mut(&receiver)? else {
                    return None;
                };
                let item = match &sequence.items {
                    Items::Range { first, step } => {
                        let yielded = contracts::add(
                            span,
                            first.clone(),
                            contracts::multiply(
                                span,
                                expr::integer(span, *step),
                                sequence.position.clone(),
                            ),
                        );
                        Value::Scalar(simplify::simplify(&yielded))
                    }
                    Items::Shared => Value::Unknown,
                };
                sequence.position =
                    contracts::add(span, sequence.position.clone(), expr::integer(span, 1));
                return Some(item);
            }
        };
        Some(Value::Iterator(sequence))
    }

    /// Observe the same index and count in the proof and finite sequence domains.
    pub(super) fn progress_bounds(&mut self, record: &Loop) -> Option<(Expr, Expr)> {
        if let Some(iterator) = &record.iterator {
            let Value::Iterator(sequence) = self.state.values.get(&iterator.receiver)? else {
                return None;
            };
            Some((sequence.position.clone(), sequence.count.clone()))
        } else {
            let control = record.control.as_ref()?;
            Some((self.scalar(&control.start)?, self.scalar(&control.end)?))
        }
    }

    /// The representative successful visit starts after this many actual visits.
    pub(super) fn bind_iterator_progress(&mut self, record: &Loop, amount: Expr) -> Option<()> {
        if let Some(iterator) = &record.iterator {
            let Value::Iterator(sequence) = self.state.values.get_mut(&iterator.receiver)? else {
                return None;
            };
            sequence.position = contracts::add(&record.span, sequence.position.clone(), amount);
        }
        Some(())
    }
}
