//! Owning extraction transfers the selected footprint independently of the
//! container's backing allocation. Option controls whether a payload exists;
//! an empty forest is the absent payload's zero charge.

use super::{
    analysis::Analysis,
    contracts,
    heap::{Owner, OwnerSlot},
    metadata::expr as metadata,
    model::unsupported,
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
                let child = option.children.remove(&OwnerSlot::Contents).ok_or_else(|| {
                    unsupported(&source.span, "an Option without a payload owner")
                })?;
                self.release_owner(option, &source.span);
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
                let (state, typ, value) = self.vector_receiver(receiver)?;
                let tag = if optional {
                    let TypX::Datatype(_, types, _) = &*typ else { unreachable!() };
                    let len = super::vectors::length(&source.span, types.clone(), value.clone());
                    let len = self.allocation_snapshot(&source.span, len);
                    Some(super::growth::select(
                        &source.span,
                        crate::ast_util::mk_ineq(
                            &source.span,
                            &contracts::literal(&source.span, 0),
                            &len,
                            InequalityOp::Lt,
                        ),
                        contracts::literal(&source.span, 1),
                        contracts::literal(&source.span, 0),
                    ))
                } else {
                    None
                };
                let (name, path) = super::paths::expr(receiver, &typ).unwrap();
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
                    let mut option = Owner { geometry: tag.clone(), ..Default::default() };
                    if !discard {
                        if elements
                            .states
                            .values()
                            .any(|id| self.growth.protected_elements.contains(id))
                        {
                            return Err(unsupported(
                                &source.span,
                                "extracting an owning child across a memory section",
                            ));
                        }
                        let parent = self.heap.root(&name).unwrap().at(&path).unwrap().clone();
                        let sources = self.capture_dependencies(&name, &path, &parent);
                        let amount = self.capture_amount(&source.span, &parent);
                        let amount = self.allocation_snapshot(&source.span, amount);
                        let payload = if optional {
                            self.layouts.option_payload(&source.typ, &source.span)?.clone()
                        } else {
                            source.typ.clone()
                        };
                        let mut child = self.input_owner(
                            &payload,
                            &source.span,
                            0,
                            &name,
                            &mut vec![],
                            &Default::default(),
                        )?;
                        self.capture_tree(&source.span, &mut child, amount, &sources);
                        if optional {
                            option.children.insert(OwnerSlot::Contents, child);
                        } else {
                            option = child;
                        }
                        self.storage.record_live(&source.span)?;
                    }
                    self.forget_collection_length(&name, &path);
                    self.finish_projections(&source.span, focused)?;
                    return Ok(Some(option));
                }
                if elements.states.values().any(|id| self.growth.protected_elements.contains(id)) {
                    return Err(unsupported(
                        &source.span,
                        "extracting an owning child across a memory section",
                    ));
                }
                let TypX::Datatype(_, types, _) = &*typ else { unreachable!() };
                let len = super::vectors::length(&source.span, types.clone(), value);
                let len =
                    SpannedTyped::new(&source.span, &crate::ast_util::int_typ(), len.x.clone());
                let index = if optional {
                    contracts::subtract(&source.span, len, contracts::literal(&source.span, 1))
                } else {
                    super::projections::spec_value(&args[1])?
                };
                let index =
                    SpannedTyped::new(&source.span, &crate::ast_util::int_typ(), index.x.clone());
                let index = self.allocation_snapshot(&source.span, index);
                let selected_path =
                    metadata::push(&source.span, metadata::path(&source.span, []), index.clone());
                let selected = metadata::subtree(
                    &source.span,
                    elements.records.clone(),
                    selected_path.clone(),
                );
                let selected = self.metadata_local(&source.span, "extracted_element", selected);
                self.metadata_partition(
                    &source.span,
                    elements.records.clone(),
                    selected_path.clone(),
                );
                let remaining = if optional {
                    metadata::without(&source.span, elements.records.clone(), selected_path)
                } else {
                    self.growth.before.entry(source.span.id).or_default().push(metadata::lemma(
                        &source.span,
                        "remove_partition",
                        vec![elements.records.clone(), index.clone()],
                    ));
                    metadata::operation(
                        &source.span,
                        "remove_index",
                        vec![elements.records.clone(), index],
                        metadata::memory_type(),
                    )
                };
                self.growth.before.entry(source.span.id).or_default().push(metadata::assign(
                    &source.span,
                    &elements.records,
                    remaining,
                ));
                self.set_element_records(&source.span, &elements, false);
                self.forget_collection_length(&name, &path);
                self.growth.vectors[state].append_only = false;
                let payload = if optional {
                    self.layouts.option_payload(&source.typ, &source.span)?.clone()
                } else {
                    source.typ.clone()
                };
                let child = self.owner_from_metadata(&source.span, &payload, selected)?;
                let mut option = Owner { geometry: tag, ..Default::default() };
                if optional {
                    option.children.insert(OwnerSlot::Contents, child);
                } else {
                    option = child;
                }
                self.storage.record_live(&source.span)?;
                self.finish_projections(&source.span, focused)?;
                Ok(Some(option))
            }
            _ => Ok(None),
        }
    }
}
