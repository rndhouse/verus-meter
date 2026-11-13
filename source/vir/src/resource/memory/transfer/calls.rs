//! Instantiate templates against tracked charge views and logical geometry.
//! Original lifetimes remain separate during the call and at its outputs.

use super::*;
use crate::resource::memory::{analysis::Analysis, heap::Owner, model::unsupported};

/// Snapshots and checked effects prepared before argument evaluation.
pub(in super::super) struct Prepared {
    /// Caller-specific costs for partitioned input lifetime identities.
    pub(in super::super) regions: BTreeMap<usize, super::super::footprint::Footprint>,
    /// Final forests and zero-charge candidates for modified borrowed parameters.
    borrowed: BTreeMap<usize, (Node, bool)>,
    /// Whether input bytes include all allocations throughout their fixed trees.
    view: super::super::metadata::View,
    /// Completed overlapping loops need requested inverse indexed views.
    ordered: bool,
    /// Disjoint caller source, intermediate-peak, and final-output identities.
    pub(in super::super) origins: super::checked::CallOrigins,
    /// Returned forest and its independently proved zero-charge candidate.
    result: Option<(Node, bool)>,
}

impl Analysis<'_> {
    pub(in super::super) fn prepare_transfer_call(
        &mut self,
        value: &Expr,
        function: &Function,
        args: &Exprs,
    ) -> Result<Option<Prepared>, VirErr> {
        let required = self.summaries[&function.x.name].transfer_required;
        let summary = &self.summaries[&function.x.name];
        // A leaf return can be selected from an internal runtime forest. Use
        // its inferred descriptor whenever the caller supplies complete owners.
        // Incoming partial views still use their checked native interface.
        if !required {
            let mut types = vec![function.x.outer_ret.x.typ.clone()];
            let mut observes_geometry = false;
            while let Some(typ) = types.pop() {
                observes_geometry |= self.layouts.cardinality(&typ);
                if self.layouts.owner(&typ) {
                    types.extend(self.layouts.owned_children(&typ, &value.span)?.into_values());
                }
            }
            // Fixed allocation trees already retain their exact byte extents.
            // Variable reservations and cardinality need descriptor specialization.
            if !observes_geometry {
                return Ok(None);
            }
            if !self.layouts.owner(&function.x.outer_ret.x.typ) || summary.transfer.is_none() {
                return Ok(None);
            }
            for (argument, parameter) in args.iter().zip(function.x.params.iter()) {
                if parameter.x.mode != Mode::Exec {
                    continue;
                }
                let typ = self.layouts.borrowed_owner(&parameter.x.typ).unwrap_or(&parameter.x.typ);
                if !self.layouts.owner(typ) {
                    continue;
                }
                let precise = super::super::paths::expr(argument, typ)
                    .and_then(|(name, path)| {
                        if self.heap.borrowed.contains_key(&name)
                            || self.growth.section_owners.contains(&name)
                        {
                            return None;
                        }
                        self.heap.root(&name).and_then(|root| root.at(&path))
                    })
                    .is_some_and(|owner| {
                        let mut complete = owner.inputs().is_empty();
                        owner.visit(&mut |node| {
                            complete &= node.view == super::super::metadata::View::Complete
                        });
                        complete
                    });
                if !precise {
                    return Ok(None);
                }
            }
        }
        let template = summary.transfer.clone().ok_or_else(|| {
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
                self.heap.check_partition(&name, &value.span)?;
            }
            let Some(owner) = self.heap.root(&name).and_then(|root| root.at(&path)) else {
                return Err(unsupported(
                    &value.span,
                    "a runtime ownership argument without a live tracked owner",
                ));
            };
            let mut precise = true;
            owner.visit(&mut |node| {
                precise &= node.geometry_known || node.source.is_some();
                precise &= node.elements.as_ref().is_none_or(|elements| {
                    elements.precise
                        && elements.inputs.is_empty()
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
        let mut origins = self.prepare_call_origins(function, args, &owners);
        let view = if owners.values().any(|owner| !owner.complete()) {
            super::super::metadata::View::Local
        } else {
            super::super::metadata::View::Complete
        };
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
            let memory = self.call_metadata(&value.span, owner, &mut proofs)?;
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
                Input::Complete => crate::ast_util::mk_bool(
                    &value.span,
                    view == super::super::metadata::View::Complete,
                ),
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
        let all_zero = owners.values().all(|owner| self.growth.owner_zero_charge(owner));
        let mut zero_values = values.clone();
        for symbol in &template.symbols {
            match symbol.input {
                Input::Forest(_) => {
                    zero_values
                        .insert(symbol.name.clone(), expr::empty(&value.span, expr::record_type()));
                }
                Input::Property(_, _, "bytes") => {
                    zero_values.insert(symbol.name.clone(), expr::integer(&value.span, 0));
                }
                _ => {}
            }
        }
        let zero = |node: &Node| {
            let cost = simplify::simplify(&expr::cost(
                &value.span,
                substitute(&node.memory, &zero_values),
                expr::integer(&value.span, 0),
            ));
            let cost = super::super::metadata::profiles::simplify(
                &cost,
                &Default::default(),
                &Default::default(),
            )
            .expect("infallible zero-charge normalization");
            all_zero && super::super::contracts::constant(&cost) == Some(0)
        };
        let borrowed = template
            .borrowed
            .iter()
            .map(|(index, node)| (*index, (instantiate_node(node, &values), zero(node))))
            .collect();
        let result = match instantiate_value(&template.result, &values) {
            Value::Owner(node) => Some((
                node,
                match &template.result {
                    Value::Owner(original) => zero(original),
                    _ => false,
                },
            )),
            _ => None,
        };
        let mut region_values = values.clone();
        for symbol in &template.symbols {
            let borrowed = match &symbol.input {
                Input::Forest(index) | Input::Property(index, _, _) => {
                    self.layouts.borrowed_owner(&function.x.params[*index].x.typ).is_some()
                }
                _ => false,
            };
            if borrowed {
                match &symbol.input {
                    Input::Forest(_) => {
                        region_values.insert(
                            symbol.name.clone(),
                            expr::empty(&value.span, expr::record_type()),
                        );
                    }
                    Input::Property(_, _, "bytes") => {
                        region_values.insert(symbol.name.clone(), expr::integer(&value.span, 0));
                    }
                    _ => {}
                }
            }
        }
        let mut regions = BTreeMap::new();
        for (id, region) in &template.regions {
            if origins.sources.values().any(|sources| !sources.is_empty()) {
                origins.peaks.insert(*id, self.transitions.fresh_region());
            }
            let region = substitute(region, &region_values);
            let mut proofs = Vec::new();
            super::proofs::forest(&value.span, &region, &mut proofs)?;
            self.growth.before.entry(value.span.id).or_default().extend(proofs);
            let amount = self.metadata_sum(&value.span, region);
            let amount = self.transfer_scalar_snapshot(&value.span, amount);
            regions.insert(
                *id,
                super::super::footprint::Footprint::charge(
                    super::super::footprint::MemoryKind::host_heap(),
                    amount,
                ),
            );
        }
        Ok(Some(Prepared { regions, borrowed, result, view, origins, ordered: template.ordered }))
    }

    fn transfer_scalar_snapshot(&mut self, span: &Span, initial: Expr) -> Expr {
        if matches!(initial.x, ExprX::Const(_)) {
            return initial;
        }
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
        self.growth.transferred_views = true;
        // Composed helpers can reconstruct fixed descriptors beneath a runtime
        // child. Selection and prefix lookup facts keep the child's own record
        // distinct from the records nested under its fixed fields. Later calls
        // must also select through descendants retained by a prior extraction.
        for group in [
            crate::fun!(CrateId::Vstd => "seq"; "group_seq_axioms"),
            expr::function("group_metadata_algebra"),
            expr::function("select_root"),
            expr::function("select_runtime"),
            expr::function("select_descendants"),
            expr::function("contains_prefix"),
            expr::function("lookup_prefix"),
            expr::function("take_children_empty"),
            expr::function("take_children_root"),
            expr::function("take_children_add"),
            expr::function("take_children_prefix"),
            expr::function("take_children_repeat"),
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
        mut prepared: Prepared,
        transferred: &mut [Option<Owner>],
    ) -> Result<Option<Owner>, VirErr> {
        for owner in transferred.iter_mut().filter_map(Option::take) {
            self.release_owner(owner, &value.span);
        }
        for (index, (node, zero)) in prepared.borrowed {
            let typ = self
                .layouts
                .borrowed_owner(&function.x.params[index].x.typ)
                .expect("mutable owner parameter");
            let (name, path) = super::super::paths::expr(&args[index], typ).ok_or_else(|| {
                unsupported(&value.span, "a transferred parameter without a tracked owner")
            })?;
            let borrowed_root = self.heap.borrowed.contains_key(&name);
            let mut old = if path.is_empty() {
                if self.heap.owners.contains_key(&name) {
                    self.heap.owners.remove(&name)
                } else {
                    self.heap.borrowed.remove(&name)
                }
            } else {
                self.heap.root_mut(&name).and_then(|root| root.take_child(&path))
            }
            .expect("validated transfer receiver");
            let replacement = self.summaries[&function.x.name]
                .allocations
                .children
                .keys()
                .any(|(parameter, _)| *parameter == index);
            let predicted =
                self.adopt_transfer_node(&value.span, node, prepared.view, zero, prepared.ordered)?;
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
            self.apply_call_origins(
                function,
                args,
                Some(index),
                &mut owner,
                &mut prepared.origins,
            )?;
            let source = super::super::projections::spec_value(&args[index])?;
            self.bind_collection_sources(&value.span, &mut owner, typ, source)?;
            if path.is_empty() {
                if borrowed_root {
                    self.heap.borrowed.insert(name, owner);
                } else {
                    self.heap.owners.insert(name, owner);
                }
            } else {
                self.heap.root_mut(&name).unwrap().replace_child(&path, owner);
            }
        }
        let mut result = prepared
            .result
            .map(|(node, zero)| {
                self.adopt_transfer_node(&value.span, node, prepared.view, zero, prepared.ordered)
            })
            .transpose()?;
        if let Some(owner) = &mut result {
            self.apply_call_origins(function, args, None, owner, &mut prepared.origins)?;
        }
        self.transitions.call_origins.insert(value.span.id, prepared.origins);
        Ok(result)
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
        old.view = predicted.view;
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

    fn adopt_transfer_node(
        &mut self,
        span: &Span,
        node: Node,
        view: super::super::metadata::View,
        zero: bool,
        ordered: bool,
    ) -> Result<Owner, VirErr> {
        let mut proofs = Vec::new();
        super::proofs::forest_views(span, &node.memory, &mut proofs, ordered)?;
        if zero {
            let check = SpannedTyped::new(
                span,
                &crate::ast_util::unit_typ(),
                ExprX::AssertAssume {
                    is_assume: false,
                    expr: crate::ast_util::mk_eq(
                        span,
                        &expr::cost(span, node.memory.clone(), expr::integer(span, 0)),
                        &expr::integer(span, 0),
                    ),
                    msg: Some(unsupported(
                        span,
                        "a transfer whose zero local charge cannot be proved",
                    )),
                },
            );
            proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(check)));
        }
        self.growth.before.entry(span.id).or_default().extend(proofs);
        let mut owner =
            self.owner_from_metadata(span, &node.typ, node.memory.clone(), view, zero)?;
        owner.visit_mut(&mut |owner| {
            owner.geometry_known = true;
        });
        /// Completed templates retain logical counts even with local byte charges.
        fn geometry(analysis: &Analysis<'_>, span: &Span, owner: &mut Owner, memory: Expr) {
            owner.geometry = Some(property(span, memory.clone(), "length"));
            for (slot, child) in &mut owner.children {
                geometry(
                    analysis,
                    span,
                    child,
                    expr::subtree(
                        span,
                        memory.clone(),
                        expr::path(span, [analysis.layouts.metadata_slot(slot)]),
                    ),
                );
            }
        }
        geometry(self, span, &mut owner, node.memory.clone());
        self.install_owner_minima(&mut owner, &node.minima);
        self.preserve_transfer_extents(span, &node.typ, node.memory, &mut owner)?;
        Ok(owner)
    }

    /// Keep structurally known byte constants available to body charge bounds.
    /// Serializing the same forest into proof locals must not turn a known
    /// allocation extent into an opaque, loop-local upper-bound expression.
    fn preserve_transfer_extents(
        &mut self,
        span: &Span,
        typ: &Typ,
        memory: Expr,
        owner: &mut Owner,
    ) -> Result<(), VirErr> {
        let mut local = memory.clone();
        for (slot, child_type) in self.layouts.owned_children(typ, span)? {
            let path = expr::path(span, [self.layouts.metadata_slot(&slot)]);
            let child = expr::subtree(span, memory.clone(), path.clone());
            self.preserve_transfer_extents(
                span,
                &child_type,
                child,
                owner.children.get_mut(&slot).expect("adopted fixed owner"),
            )?;
            local = expr::without(span, local, path);
        }
        if self.layouts.owning_elements(typ) {
            local = expr::operation(span, "nonruntime", vec![local], expr::memory_type());
        }
        let amount = simplify::simplify(&expr::cost(span, local, expr::integer(span, 0)));
        if super::super::contracts::constant(&amount).is_some() {
            owner.extent = Some(amount.clone());
            if let Some(id) = owner.vector {
                self.growth.vectors[id].backing.initial_bytes = amount.clone();
                self.growth.vectors[id].backing.floor = amount;
            }
        }
        Ok(())
    }
}
