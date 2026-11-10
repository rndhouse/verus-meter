//! Instantiate a template against snapshots of locally modeled owners. Peak
//! profiles still keep incoming allocations live throughout the helper call.

use super::*;
use crate::resource::memory::{analysis::Analysis, heap::Owner, model::unsupported};

pub(in super::super) struct Prepared {
    borrowed: BTreeMap<usize, Node>,
    result: Option<Node>,
}

impl Analysis<'_> {
    pub(in super::super) fn prepare_transfer_call(
        &mut self,
        value: &Expr,
        function: &Function,
        args: &Exprs,
    ) -> Result<Option<Prepared>, VirErr> {
        if !super::required(function, self.layouts)? {
            return Ok(None);
        }
        let template = self.summaries[&function.x.name].transfer.clone().ok_or_else(|| {
            unsupported(&value.span, "a runtime ownership call without a precise helper summary")
        })?;
        // Determine eligibility without changing accounting or scheduling proofs.
        let mut owners = BTreeMap::new();
        for (index, (argument, parameter)) in args.iter().zip(function.x.params.iter()).enumerate()
        {
            if parameter.x.mode != Mode::Exec {
                continue;
            }
            let typ = self.layouts.borrowed_owner(&parameter.x.typ).unwrap_or(&parameter.x.typ);
            if !self.layouts.owner(typ) {
                continue;
            }
            let Some((name, path)) = super::super::paths::expr(argument, typ) else {
                return Err(unsupported(
                    &value.span,
                    "a runtime ownership argument without a tracked owner; bind the argument first",
                ));
            };
            if self.growth.section_owners.contains(&name) {
                return Err(unsupported(
                    &value.span,
                    "runtime ownership transfers across a memory section",
                ));
            }
            if !super::super::paths::indexed(&path)
                && self.summaries[&function.x.name]
                    .allocations
                    .children
                    .keys()
                    .any(|(parameter, _)| *parameter == index)
            {
                self.heap.check_transfer(&name, &value.span)?;
            }
            if self.heap.borrowed.contains_key(&name) {
                return Err(unsupported(
                    &value.span,
                    "a runtime ownership call without precise argument metadata",
                ));
            }
            let Some(owner) = self.heap.root(&name).and_then(|root| root.at(&path)) else {
                return Err(unsupported(
                    &value.span,
                    "a runtime ownership argument without a live tracked owner",
                ));
            };
            let mut precise = owner.inputs().is_empty();
            owner.visit(&mut |node| {
                precise &= node.geometry_known || node.source.is_some();
                precise &= node.elements.as_ref().is_none_or(|elements| {
                    elements.precise
                        && elements
                            .states
                            .values()
                            .all(|id| !self.growth.protected_elements.contains(id))
                });
                precise &=
                    node.vector.is_none_or(|id| !self.growth.section_protected.contains(&id));
            });
            if !precise {
                return Err(unsupported(
                    &value.span,
                    "a runtime ownership call without precise argument metadata",
                ));
            }
            owners.insert(index, owner.clone());
        }
        for argument in args.iter() {
            self.check_projection_effects(argument)?;
        }
        let mut scalar = BTreeMap::new();
        for symbol in &template.symbols {
            if let Input::Scalar(index) = symbol.input {
                let Ok(pure) = super::super::projections::spec_value(&args[index]) else {
                    return Err(unsupported(
                        &value.span,
                        "a computed scalar in a runtime ownership call; bind the argument first",
                    ));
                };
                scalar.insert(index, pure);
            }
        }
        self.enable_transfer_algebra(&value.span);
        let mut forests = BTreeMap::new();
        let mut minima = BTreeMap::new();
        for (index, owner) in &owners {
            let mut records = Vec::new();
            owner.visit(&mut |node| {
                if let Some(elements) = &node.elements {
                    records.push(elements.records.clone());
                }
            });
            for records in records {
                self.growth
                    .before
                    .entry(value.span.id)
                    .or_default()
                    .push(super::super::metadata::runtime_shape_proof(&value.span, records));
            }
            let mut proofs = Vec::new();
            let memory = self.owner_metadata(&value.span, owner, &mut proofs);
            super::proofs::forest(&value.span, &memory, &mut proofs)?;
            self.growth.before.entry(value.span.id).or_default().extend(proofs);
            forests.insert(*index, self.metadata_local(&value.span, "call_records", memory));
            let mut facts = Minima::new();
            self.owner_minima(owner, &mut vec![], &mut facts);
            minima.insert(*index, facts);
        }
        let mut scalar_snapshots = BTreeMap::new();
        for (index, pure) in scalar {
            scalar_snapshots.insert(index, self.transfer_scalar_snapshot(&value.span, pure));
        }
        let mut values = HashMap::new();
        for symbol in &template.symbols {
            let replacement = match &symbol.input {
                Input::Scalar(index) => scalar_snapshots[index].clone(),
                Input::Forest(index) => forests[index].clone(),
                Input::Property(index, path, field) => {
                    let owner = owners[index].at(path).expect("fixed template input path");
                    let initial = match *field {
                        "length" => self.owner_length(&value.span, owner),
                        "capacity" => owner
                            .vector
                            .map(|id| self.growth.vectors[id].capacity.clone())
                            .or_else(|| owner.capacity.clone())
                            .unwrap_or_else(|| expr::integer(&value.span, 0)),
                        "bytes" => {
                            let fixed = super::super::contracts::literal(&value.span, owner.bytes);
                            owner.dynamic.map_or(fixed.clone(), |id| {
                                super::super::contracts::add(
                                    &value.span,
                                    fixed,
                                    self.storage.dynamic_cost(&value.span, id),
                                )
                            })
                        }
                        _ => unreachable!("template root property"),
                    };
                    self.transfer_scalar_snapshot(&value.span, initial)
                }
                Input::Minimum(index, path) => minima[index]
                    .get(path)
                    .map(|floor| floor.capacity.clone())
                    .unwrap_or_else(|| expr::integer(&value.span, 0)),
            };
            values.insert(symbol.name.clone(), replacement);
        }
        let borrowed = template
            .borrowed
            .iter()
            .map(|(index, node)| (*index, instantiate_node(node, &values)))
            .collect();
        let result = match instantiate_value(&template.result, &values) {
            Value::Owner(node) => Some(node),
            _ => None,
        };
        Ok(Some(Prepared { borrowed, result }))
    }

    fn transfer_scalar_snapshot(&mut self, span: &Span, initial: Expr) -> Expr {
        let (value, declaration) =
            expr::local(span, "call_scalar", initial.typ.clone(), initial.clone(), Mode::Spec);
        let StmtX::Decl { pattern, mode, els, assert_irrefutable, .. } = &declaration.x else {
            unreachable!()
        };
        self.growth.declarations.push(crate::def::Spanned::new(
            span.clone(),
            StmtX::Decl {
                pattern: pattern.clone(),
                mode: *mode,
                init: None,
                els: els.clone(),
                assert_irrefutable: *assert_irrefutable,
            },
        ));
        self.growth.before.entry(span.id).or_default().push(expr::assign(span, &value, initial));
        value
    }

    fn enable_transfer_algebra(&mut self, span: &Span) {
        for group in [
            crate::fun!(CrateId::Vstd => "seq"; "group_seq_axioms"),
            crate::fun!(CrateId::Vstd => "std_specs", "memory"; "group_metadata_algebra"),
            crate::fun!(CrateId::Vstd => "std_specs", "memory"; "select_root"),
            crate::fun!(CrateId::Vstd => "std_specs", "memory"; "take_children_add"),
            crate::fun!(CrateId::Vstd => "std_specs", "memory"; "take_children_prefix"),
            crate::fun!(CrateId::Vstd => "std_specs", "memory"; "take_children_repeat"),
        ] {
            let activation =
                SpannedTyped::new(span, &crate::ast_util::unit_typ(), ExprX::Fuel(group, 1, true));
            self.growth
                .before
                .entry(span.id)
                .or_default()
                .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(activation)));
        }
    }

    pub(in super::super) fn apply_transfer_call(
        &mut self,
        value: &Expr,
        function: &Function,
        args: &Exprs,
        prepared: Prepared,
        transferred: &mut [Option<Owner>],
    ) -> Result<Option<Owner>, VirErr> {
        for owner in transferred.iter_mut().filter_map(Option::take) {
            self.release_owner(owner, &value.span);
        }
        for (index, node) in prepared.borrowed {
            let typ = self
                .layouts
                .borrowed_owner(&function.x.params[index].x.typ)
                .expect("mutable owner parameter");
            let (name, path) = super::super::paths::expr(&args[index], typ).ok_or_else(|| {
                unsupported(&value.span, "a transferred parameter without a tracked owner")
            })?;
            let mut old = if path.is_empty() {
                self.heap.owners.remove(&name)
            } else {
                self.heap.root_mut(&name).and_then(|root| root.take_child(&path))
            }
            .expect("validated transfer receiver");
            let replacement = self.summaries[&function.x.name]
                .allocations
                .children
                .keys()
                .any(|(parameter, _)| *parameter == index);
            let predicted = self.adopt_transfer_node(&value.span, node)?;
            let mut owner = if replacement {
                self.release_owner(old, &value.span);
                predicted
            } else {
                let effects = self.summaries[&function.x.name].allocations.retained.clone();
                let bound = super::super::contracts::instantiate(
                    function,
                    args,
                    &self.stable_scalars,
                    self.budgets,
                    self.functions,
                    self.layouts,
                    false,
                )
                .unwrap_or_else(|_| {
                    super::super::contracts::literal(&value.span, self.budgets[&function.x.name])
                });
                self.commit_transfer_owner(
                    &value.span,
                    &mut old,
                    &predicted,
                    index,
                    &mut vec![],
                    &effects,
                    &bound,
                )?;
                self.release_owner_storage(predicted, &value.span, false);
                old
            };
            let source = super::super::projections::spec_value(&args[index])?;
            self.bind_collection_sources(&value.span, &mut owner, typ, source)?;
            if path.is_empty() {
                self.heap.owners.insert(name, owner);
            } else {
                self.heap.root_mut(&name).unwrap().replace_child(&path, owner);
            }
        }
        prepared.result.map(|node| self.adopt_transfer_node(&value.span, node)).transpose()
    }

    fn commit_transfer_owner(
        &mut self,
        span: &Span,
        old: &mut Owner,
        predicted: &Owner,
        parameter: usize,
        path: &mut super::super::heap::OwnerPath,
        effects: &HashMap<super::super::paths::InputPath, super::super::footprint::Charge<Expr>>,
        bound: &Expr,
    ) -> Result<(), VirErr> {
        if let (Some(id), Some(next)) = (old.vector, predicted.vector) {
            if effects.contains_key(&(parameter, path.clone())) {
                let source = self.growth.vectors[next].clone();
                let state = &mut self.growth.vectors[id];
                self.growth.after.entry(span.id).or_default().extend([
                    super::super::symbolic::assign(span, &state.capacity, source.capacity),
                    super::super::symbolic::assign(
                        span,
                        &state.backing.bytes,
                        source.backing.bytes,
                    ),
                ]);
                state.backing.changed = true;
                state.backing.floor = super::super::contracts::maximum(
                    span,
                    state.backing.floor.clone(),
                    bound.clone(),
                );
                state.sequence_length = None;
                state.append_only = false;
            }
        }
        if let (Some(old), Some(new)) = (&mut old.elements, &predicted.elements) {
            self.commit_transferred_elements(span, old, new);
        }
        for (slot, child) in &mut old.children {
            path.push(slot.clone());
            self.commit_transfer_owner(
                span,
                child,
                predicted.children.get(slot).ok_or_else(|| {
                    unsupported(span, "a transferred owner with an incomplete fixed layout")
                })?,
                parameter,
                path,
                effects,
                bound,
            )?;
            path.pop();
        }
        Ok(())
    }

    fn adopt_transfer_node(&mut self, span: &Span, node: Node) -> Result<Owner, VirErr> {
        let mut proofs = Vec::new();
        super::proofs::forest(span, &node.memory, &mut proofs)?;
        self.growth.before.entry(span.id).or_default().extend(proofs);
        let mut owner = self.owner_from_metadata(span, &node.typ, node.memory)?;
        self.install_owner_minima(&mut owner, &node.minima);
        Ok(owner)
    }
}
