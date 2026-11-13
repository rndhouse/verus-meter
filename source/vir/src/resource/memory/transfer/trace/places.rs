//! Resolve checked owner locations and apply reads, moves, and replacements.
//!
//! Source expressions supply index values. Authoritative paths and move
//! decisions come from body accounting, not from inspecting source types alone.

use super::*;
use crate::resource::memory::{metadata, paths};

impl Trace<'_> {
    /// Evaluate index operands used by a checked source ownership projection.
    fn indices_expr(&mut self, value: &Expr, result: &mut HashMap<u64, Expr>) -> Option<()> {
        if let Some(args) = paths::vector_index(value) {
            self.indices_expr(&args[0], result)?;
            result.insert(value.span.id, self.scalar(&args[1])?);
        } else {
            match &value.x {
                ExprX::ReadPlace(place, _)
                | ExprX::BorrowMut(place)
                | ExprX::TwoPhaseBorrowMut(place) => self.indices_place(place, result)?,
                ExprX::UnaryOpr(UnaryOpr::Field(_), base)
                | ExprX::Unary(UnaryOp::MutRefCurrent, base) => self.indices_expr(base, result)?,
                _ => {}
            }
        }
        Some(())
    }

    /// Collect index operands while following a source place to its base.
    fn indices_place(&mut self, place: &Place, result: &mut HashMap<u64, Expr>) -> Option<()> {
        match &place.x {
            PlaceX::Temporary(value) => self.indices_expr(value, result)?,
            PlaceX::Field(_, base) | PlaceX::DerefMut(base) => self.indices_place(base, result)?,
            PlaceX::Index(base, index, _, _) => {
                self.indices_place(base, result)?;
                result.insert(place.span.id, self.scalar(index)?);
            }
            _ => {}
        }
        Some(())
    }

    /// Combine an authoritative owner path with its traced runtime indices.
    pub(super) fn checked_location(&mut self, place: &checked::Place) -> Option<Location> {
        let (name, path) = &place.location;
        let mut indices = HashMap::new();
        self.indices_expr(&place.source, &mut indices)?;
        let expressions = path
            .iter()
            .map(|slot| match slot {
                OwnerSlot::Element(id) => indices.get(id).cloned(),
                _ => Some(expr::integer(&place.source.span, self.layouts.metadata_slot(slot))),
            })
            .collect::<Option<Vec<_>>>()?;
        Some((name.clone(), path.clone(), expressions))
    }

    /// Build a finite metadata path from evaluated ownership steps.
    pub(super) fn path(span: &Span, steps: &[Expr]) -> Expr {
        steps.iter().fold(expr::path(span, []), |path, step| expr::push(span, path, step.clone()))
    }

    /// Classify fixed and repeated reservation steps independently of runtime indices.
    fn class(path: &[OwnerSlot]) -> Vec<Step> {
        path.iter()
            .map(|slot| match slot {
                OwnerSlot::Element(_) => Step::Repeated,
                _ => Step::Fixed(slot.clone()),
            })
            .collect()
    }

    /// Select an owner and its reservation minima without consuming it.
    pub(super) fn get(&self, span: &Span, location: &Location, typ: &Typ) -> Option<Node> {
        let Value::Owner(root) = self.state.values.get(&location.0)? else {
            return None;
        };
        let class = Self::class(&location.1);
        let minima = root
            .minima
            .iter()
            .filter_map(|(path, floor)| {
                path.strip_prefix(class.as_slice()).map(|rest| (rest.to_vec(), floor.clone()))
            })
            .collect();
        // Select one ownership edge at a time, matching the finite projection
        // algebra used by local borrows. A repeated edge can then expose the
        // fixed layout below it without flattening arbitrary composite paths.
        let memory = location.2.iter().fold(root.memory.clone(), |memory, step| {
            expr::subtree(span, memory, Self::path(span, std::slice::from_ref(step)))
        });
        Some(Node {
            origin: if location.1.is_empty() { root.origin } else { None },
            typ: typ.clone(),
            memory,
            minima,
        })
    }

    /// Replace a selected owner while recording mutation and updating reservation minima.
    pub(super) fn set(&mut self, span: &Span, location: &Location, child: Node) -> Option<()> {
        self.effects.push(Effect::Mutation(location.0.clone()));
        if location.1.is_empty() {
            self.state.values.insert(location.0.clone(), Value::Owner(child));
        } else {
            let Value::Owner(root) = self.state.values.get_mut(&location.0)? else {
                return None;
            };
            root.origin = None;
            let mut parents = Vec::new();
            let mut selected = root.memory.clone();
            for step in &location.2 {
                let path = Self::path(span, std::slice::from_ref(step));
                parents.push((selected.clone(), path.clone()));
                selected = expr::subtree(span, selected, path);
            }
            root.memory = parents.into_iter().rev().fold(child.memory, |memory, (parent, path)| {
                metadata::operations::replace(span, parent, path, memory)
            });
            let class = Self::class(&location.1);
            if !class.iter().any(|step| matches!(step, Step::Repeated)) {
                root.minima.retain(|path, _| !path.starts_with(&class));
            }
            let child = child
                .minima
                .into_iter()
                .map(|(path, floor)| (class.iter().cloned().chain(path).collect(), floor))
                .collect();
            join_minima(span, &mut root.minima, &child);
        }
        self.state.written.insert(location.0.clone());
        Some(())
    }

    /// Consume a checked owner location, leaving its containing forest updated.
    pub(super) fn take(&mut self, span: &Span, location: &Location, typ: &Typ) -> Option<Node> {
        let child = self.get(span, location, typ)?;
        if location.1.is_empty() {
            self.effects.push(Effect::Mutation(location.0.clone()));
            self.state.values.remove(&location.0);
        } else {
            self.set(
                span,
                location,
                Node {
                    origin: None,
                    typ: typ.clone(),
                    memory: expr::empty(span, expr::record_type()),
                    minima: Minima::new(),
                },
            )?;
        }
        Some(child)
    }

    /// Read a scalar place or consume the move recorded for an owning place.
    pub(super) fn place_value(&mut self, place: &Place, typ: &Typ) -> Option<Value> {
        if let PlaceX::Temporary(value) = &place.x {
            return self.value(value);
        }
        if let Some(transition) = self.checked.moves.get(&place.span.id).cloned() {
            self.used.insert((checked::Kind::Move, place.span.id));
            let location = self.checked_location(&transition)?;
            return Some(Value::Owner(self.take(&place.span, &location, &transition.typ)?));
        }
        if self.layouts.owner(typ) {
            return None;
        }
        // A scalar read through a box does not consume the outer owner. Its
        // value may be irrelevant to ownership inference, but its actual result
        // type must govern this decision rather than the enclosing place type.
        if let PlaceX::Local(name) = &place.x {
            return Some(match self.state.values.get(name) {
                Some(Value::Owner(_)) => Value::Unknown,
                value => value.cloned().unwrap_or(Value::Unknown),
            });
        }
        self.place_effects(place)?;
        Some(Value::Unknown)
    }

    /// Evaluate a place's temporary and index effects without moving its owner.
    fn place_effects(&mut self, place: &Place) -> Option<()> {
        match &place.x {
            PlaceX::Temporary(value) => {
                self.value(value)?;
            }
            PlaceX::Field(_, base) | PlaceX::DerefMut(base) => self.place_effects(base)?,
            PlaceX::Index(base, index, _, _) => {
                self.place_effects(base)?;
                self.value(index)?;
            }
            PlaceX::Local(_) => {}
            _ => return None,
        }
        Some(())
    }
}
