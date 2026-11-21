//! Owning extraction transfers the selected footprint independently of the
//! container's backing allocation. Option controls whether a payload exists;
//! an empty forest is the absent payload's zero charge.

use super::{
    analysis::Analysis,
    heap::{Owner, OwnerSlot},
    metadata::{expr as metadata, operations::Removal},
    model::unsupported,
    workers::SelectedWorker,
};
use crate::ast::*;

impl Analysis<'_> {
    pub(super) fn extracted_owner(
        &mut self,
        source: &Expr,
        discard: bool,
    ) -> Result<Option<Owner>, VirErr> {
        let source = match &source.x {
            ExprX::ReadPlace(place, _) if discard => match &place.x {
                PlaceX::Temporary(value) => value,
                _ => source,
            },
            _ => source,
        };
        if !self.layouts.owner(&source.typ) {
            return Ok(None);
        }
        let ExprX::Call {
            target: CallTarget::Fun(_, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &source.x
        else {
            return Ok(None);
        };
        match attrs.resource_intrinsic {
            Some(ResourceIntrinsic::OptionUnwrap) => {
                let [arg] = args.as_slice() else {
                    return Err(unsupported(&source.span, "this Option extraction"));
                };
                // Intrinsic pop shares the payload destination. An ordinary
                // call returning Option still needs its declared result slot.
                let mut value = arg;
                while let ExprX::ReadPlace(place, _) = &value.x {
                    let PlaceX::Temporary(inner) = &place.x else { break };
                    value = inner;
                }
                let pop = matches!(&value.x, ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. }
                    if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPop));
                if pop {
                    self.initialize_expr(arg)?;
                } else {
                    let slot = self.produce(arg)?;
                    self.release_value(slot, &source.span);
                }
                let mut option = self
                    .result_owner
                    .take()
                    .ok_or_else(|| unsupported(&source.span, "an Option without ownership"))?;
                if !self.select_optional_guard(&mut option, true, &source.span)? {
                    return Err(unsupported(
                        &source.span,
                        "a guard extraction without a present acquisition",
                    ));
                }
                let child = option.children.remove(&OwnerSlot::Contents).ok_or_else(|| {
                    unsupported(&source.span, "an Option without a payload owner")
                })?;
                self.release_owner(option, &source.span);
                self.transitions.operation(
                    &source.span,
                    super::transfer::checked::Operation::Unwrap {
                        source: arg.clone(),
                        observed_scalar: false,
                    },
                );
                Ok(Some(child))
            }
            Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove) => {
                let optional = attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPop);
                let Some(receiver) = args.first() else {
                    return Err(unsupported(&source.span, "this vector extraction"));
                };
                if args.len() != if optional { 1 } else { 2 } {
                    return Err(unsupported(&source.span, "this vector extraction"));
                }
                if !optional {
                    self.discard(&args[1])?;
                }
                let focused = self.focus_arguments(args, &source.span)?;
                let resolved = self.vector_receiver(receiver, &source.span)?;
                let state = resolved.state;
                let typ = resolved.typ.clone();
                let pop = if optional {
                    let len = resolved.length.clone();
                    let len =
                        SpannedTyped::new(&source.span, &crate::ast_util::int_typ(), len.x.clone());
                    let len = self.allocation_snapshot(&source.span, len);
                    Some(Removal::pop(&source.span, len))
                } else {
                    None
                };
                self.remove_vector_slot(&source.span, state, resolved.length.clone());
                self.advance_protected_vector(&source.span, &resolved, attrs.resource_intrinsic);
                let tag = pop.as_ref().and_then(|removal| removal.tag.clone());
                let (name, path) = resolved.location.clone();
                let elements = self
                    .heap
                    .root(&name)
                    .unwrap()
                    .at(&path)
                    .unwrap()
                    .elements
                    .as_ref()
                    .unwrap()
                    .clone();
                if !elements.precise {
                    return Err(unsupported(
                        &source.span,
                        "extracting a child without precise allocation metadata",
                    ));
                }
                if elements.view == super::metadata::View::Local {
                    // A borrowed input stays charged to the caller throughout
                    // this frame. Partition only the helper's new charges here;
                    // the checked template partitions the complete forest at
                    // the call site. Pop's tag comes from the executable length,
                    // not the local forest, which may be empty for a live child.
                    // Owned extraction additionally partitions incoming lifetimes.
                    // An empty pop's selected input regions are empty too; its
                    // remaining region still includes the collection backing.
                    self.heap.check_partition(&name, &source.span)?;
                }
                if elements.states.values().any(|id| self.growth.protected_elements.contains(id)) {
                    return Err(unsupported(
                        &source.span,
                        "extracting an owning child across a memory section",
                    ));
                }
                let mut removal = if let Some(pop) = pop {
                    pop
                } else {
                    let len = resolved.length.clone();
                    let len =
                        SpannedTyped::new(&source.span, &crate::ast_util::int_typ(), len.x.clone());
                    let index = super::projections::spec_value(&args[1])?;
                    let index = SpannedTyped::new(
                        &source.span,
                        &crate::ast_util::int_typ(),
                        index.x.clone(),
                    );
                    Removal::remove(&source.span, len, index)
                };
                removal.index = self.allocation_snapshot(&source.span, removal.index);
                let partition = removal.partition(&source.span, elements.records.clone());
                let selected =
                    self.metadata_local(&source.span, "extracted_element", partition.selected);
                if elements.references == super::elements::References::IndexedAliases && optional {
                    // Partition the pre-pop forest before committing the removal.
                    let proofs = self.growth.before.entry(source.span.id).or_default();
                    for root in self.growth.indexed_shared.keys() {
                        proofs.push(metadata::lemma(
                            &source.span,
                            "shared_count_pop",
                            vec![
                                elements.records.clone(),
                                removal.path(&source.span),
                                metadata::integer(&source.span, root.serial()),
                            ],
                        ));
                    }
                }
                if optional
                    && let ExprX::Var(forest) = &elements.records.x
                    && let Some(families) = self.growth.forest_families.get(forest)
                    && families.len() > 1
                    && self
                        .growth
                        .indexed_shared
                        .values()
                        .any(|claims| claims.population.uniform_weight(families.iter()).is_none())
                {
                    // The selected family's weight is needed again when a joined
                    // result releases its Arc. Instantiate the pop law on the
                    // pre-pop forest while the occupied prefix is still available.
                    let last = removal.length.clone();
                    let path = metadata::push(
                        &source.span,
                        metadata::path(&source.span, []),
                        last.clone(),
                    );
                    let proofs = self.growth.before.entry(source.span.id).or_default();
                    for family in families {
                        proofs.push(metadata::lemma(
                            &source.span,
                            "worker_family_count_pop",
                            vec![
                                elements.records.clone(),
                                path.clone(),
                                last.clone(),
                                metadata::path(&source.span, family.descriptor()),
                            ],
                        ));
                    }
                }
                self.metadata_partition(
                    &source.span,
                    elements.records.clone(),
                    removal.path(&source.span),
                );
                if !optional {
                    self.growth.before.entry(source.span.id).or_default().push(metadata::lemma(
                        &source.span,
                        "remove_partition",
                        vec![elements.records.clone(), removal.index.clone()],
                    ));
                }
                if !optional && self.growth.loop_depth > 0 {
                    // Reestablish quantified reservation invariants for the
                    // shifted survivors. Straight-line proofs need only the
                    // selected partition, avoiding unrelated indexed views.
                    self.growth.before.entry(source.span.id).or_default().push(metadata::lemma(
                        &source.span,
                        "remove_index_views",
                        vec![elements.records.clone(), removal.index.clone()],
                    ));
                }
                self.growth.before.entry(source.span.id).or_default().push(metadata::assign(
                    &source.span,
                    &elements.records,
                    partition.remaining,
                ));
                self.set_element_records(&source.span, &elements, false);
                self.forget_collection_length(&name, &path);
                self.growth.vectors[state].append_only = false;
                let payload = if optional {
                    self.layouts.option_payload(&source.typ, &source.span)?.clone()
                } else {
                    source.typ.clone()
                };
                let mut child = if self
                    .transitions
                    .worker_parameter
                    .is_some_and(|(_, vector)| vector == state)
                {
                    Owner { selected_worker: Some(SelectedWorker::Parameter), ..Default::default() }
                } else if matches!(&*payload, TypX::Decorate(TypDecoration::Arc, _, _))
                    && elements.references == super::elements::References::IndexedAliases
                {
                    if !optional {
                        return Err(unsupported(
                            &source.span,
                            "reindexing stored Arc reservations",
                        ));
                    }
                    self.take_selected_slot(&source.span, selected)?
                } else if !self.growth.occurrence_peers.is_empty()
                    && self.layouts.join_handle(&payload).is_some()
                    && let ExprX::Var(forest) = &elements.records.x
                    && let Some(families) =
                        self.growth.forest_families.get(forest).cloned().filter(|f| !f.is_empty())
                {
                    self.worker_from_metadata(
                        &source.span,
                        &payload,
                        selected,
                        elements.view,
                        elements.zero_charge(&self.growth),
                        Some(families),
                    )?
                } else {
                    self.owner_from_metadata(
                        &source.span,
                        &payload,
                        selected,
                        elements.view,
                        elements.zero_charge(&self.growth),
                    )?
                };
                let input = self.split_input(
                    &source.span,
                    &(name.clone(), path.clone()),
                    Some(&mut child),
                )?;
                let mut option = Owner { geometry: tag, ..Default::default() };
                if optional {
                    option.children.insert(OwnerSlot::Contents, child);
                } else {
                    option = child;
                }
                self.storage.record_live(&source.span)?;
                self.transitions.operation(
                    &source.span,
                    super::transfer::checked::Operation::Remove {
                        receiver: super::transfer::checked::Place {
                            source: receiver.clone(),
                            typ,
                            location: (name, path),
                        },
                        index: args.get(1).cloned(),
                        input,
                    },
                );
                self.finish_projections(&source.span, focused)?;
                Ok(Some(option))
            }
            _ => Ok(None),
        }
    }
}
