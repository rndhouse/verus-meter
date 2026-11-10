//! Container operation adapters for finite ownership transformations.

use super::*;
use crate::resource::memory::metadata::operations::Removal;

impl Trace<'_> {
    pub(super) fn call(
        &mut self,
        value: &Expr,
        target: &Fun,
        intrinsic: Option<ResourceIntrinsic>,
        args: &Exprs,
    ) -> Option<Value> {
        let span = &value.span;
        match intrinsic {
            Some(ResourceIntrinsic::ArrayRepeat) => {
                for argument in args.iter() {
                    self.value(argument)?;
                }
                Some(Value::Unknown)
            }
            Some(ResourceIntrinsic::VecNew | ResourceIntrinsic::VecWithCapacity) => {
                let capacity =
                    if args.is_empty() { expr::integer(span, 0) } else { self.scalar(&args[0])? };
                let element = self.layouts.vector_element(&value.typ, span).ok()?;
                let memory = expr::push(
                    span,
                    expr::empty(span, expr::record_type()),
                    allocated(
                        span,
                        contracts::multiply(
                            span,
                            capacity.clone(),
                            contracts::literal(span, element),
                        ),
                        capacity.clone(),
                        expr::integer(span, 0),
                    ),
                );
                Some(Value::Owner(Node {
                    typ: value.typ.clone(),
                    memory,
                    minima: [(vec![], Floor { capacity, element })].into(),
                }))
            }
            Some(ResourceIntrinsic::BoxNew) => {
                let child = self.value(args.first()?)?;
                let crate::resource::memory::layout::AllocationLayout::Fixed(bytes) =
                    self.layouts.box_layout(&value.typ, span).ok()??
                else {
                    return None;
                };
                let mut memory = expr::push(
                    span,
                    expr::empty(span, expr::record_type()),
                    allocated(
                        span,
                        contracts::literal(span, bytes),
                        expr::integer(span, 0),
                        expr::integer(span, 0),
                    ),
                );
                let mut minima = Minima::new();
                if let Value::Owner(child) = child {
                    memory = expr::add(
                        span,
                        memory,
                        expr::prefix(
                            span,
                            child.memory,
                            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                        ),
                    );
                    minima.extend(child.minima.into_iter().map(|(path, floor)| {
                        (
                            std::iter::once(Step::Fixed(OwnerSlot::Contents)).chain(path).collect(),
                            floor,
                        )
                    }));
                }
                Some(Value::Owner(Node { typ: value.typ.clone(), memory, minima }))
            }
            Some(ResourceIntrinsic::VecLen) => {
                let (location, node) = self.receiver(args.first()?)?;
                self.effects.push(loops::Effect::Read(location.0));
                Some(Value::Scalar(property(span, node.memory, "length")))
            }
            Some(ResourceIntrinsic::VecPush) => {
                let (location, mut node) = self.receiver(args.first()?)?;
                let child = self.value(args.get(1)?)?;
                let appended = child.clone();
                let length = property(span, node.memory.clone(), "length");
                let (capacity, bytes, _) = growth::push_transition(
                    span,
                    property(span, node.memory.clone(), "capacity"),
                    property(span, node.memory.clone(), "bytes"),
                    length.clone(),
                    self.layouts.vector_element(&node.typ, span).ok()?,
                    true,
                );
                if let Value::Owner(child) = child {
                    self.appends = true;
                    let path = expr::push(span, expr::path(span, []), length.clone());
                    node.memory =
                        expr::add(span, node.memory, expr::prefix(span, child.memory, path));
                    let children = child
                        .minima
                        .into_iter()
                        .map(|(path, floor)| {
                            (std::iter::once(Step::Repeated).chain(path).collect(), floor)
                        })
                        .collect();
                    join_minima(span, &mut node.minima, &children);
                }
                node.memory = with_root(
                    span,
                    node.memory,
                    bytes,
                    capacity,
                    contracts::add(span, length, expr::integer(span, 1)),
                    self.layouts.owning_elements(&node.typ),
                );
                let typ = node.typ.clone();
                self.set(span, &location, node)?;
                if self.branch_depth == 0 {
                    self.effects.pop();
                    self.effects.push(loops::Effect::Append(location, typ, appended));
                }
                Some(Value::Unit)
            }
            Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove) => {
                let optional = intrinsic == Some(ResourceIntrinsic::VecPop);
                let (location, mut node) = self.receiver(args.first()?)?;
                let length = property(span, node.memory.clone(), "length");
                let removal = if optional {
                    Removal::pop(span, length)
                } else {
                    Removal::remove(span, length, self.scalar(args.get(1)?)?)
                };
                let partition = removal.partition(span, node.memory.clone());
                let next = with_root(
                    span,
                    partition.remaining,
                    property(span, node.memory.clone(), "bytes"),
                    property(span, node.memory.clone(), "capacity"),
                    removal.length,
                    self.layouts.owning_elements(&node.typ),
                );
                let mut minima: Minima = node
                    .minima
                    .iter()
                    .filter_map(|(path, floor)| {
                        path.strip_prefix(&[Step::Repeated])
                            .map(|rest| (rest.to_vec(), floor.clone()))
                    })
                    .collect();
                node.memory = next;
                let typ = node.typ.clone();
                self.set(span, &location, node)?;
                if optional && self.branch_depth == 0 {
                    self.effects.pop();
                    self.effects.push(loops::Effect::Pop(location, typ));
                }
                if !self.layouts.owner(&value.typ) {
                    return Some(Value::Unknown);
                }
                let memory = if optional {
                    minima = minima
                        .into_iter()
                        .map(|(path, floor)| {
                            (
                                std::iter::once(Step::Fixed(OwnerSlot::Contents))
                                    .chain(path)
                                    .collect(),
                                floor,
                            )
                        })
                        .collect();
                    let tag = removal.tag.expect("pop result tag");
                    expr::add(
                        span,
                        expr::push(
                            span,
                            expr::empty(span, expr::record_type()),
                            allocated(span, expr::integer(span, 0), expr::integer(span, 0), tag),
                        ),
                        expr::prefix(
                            span,
                            partition.selected,
                            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                        ),
                    )
                } else {
                    partition.selected
                };
                Some(Value::Owner(Node { typ: value.typ.clone(), memory, minima }))
            }
            Some(ResourceIntrinsic::OptionUnwrap) => {
                let Value::Owner(node) = self.value(args.first()?)? else {
                    return Some(Value::Unknown);
                };
                let minima = node
                    .minima
                    .into_iter()
                    .filter_map(|(path, floor)| {
                        path.strip_prefix(&[Step::Fixed(OwnerSlot::Contents)])
                            .map(|rest| (rest.to_vec(), floor))
                    })
                    .collect();
                Some(Value::Owner(Node {
                    typ: value.typ.clone(),
                    memory: expr::subtree(
                        span,
                        node.memory,
                        expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                    ),
                    minima,
                }))
            }
            Some(ResourceIntrinsic::OptionIsSome | ResourceIntrinsic::OptionIsNone) => {
                let typ = crate::resource::memory::paths::referent(&args.first()?.typ);
                let location = self.location(&args[0], typ)?;
                let node = self.get(span, &location, typ)?;
                let some =
                    mk_eq(span, &property(span, node.memory, "length"), &expr::integer(span, 1));
                let condition = if intrinsic == Some(ResourceIntrinsic::OptionIsSome) {
                    some
                } else {
                    SpannedTyped::new(span, &bool_typ(), ExprX::Unary(UnaryOp::Not, some))
                };
                Some(Value::Scalar(condition))
            }
            Some(ResourceIntrinsic::VecIntoBoxedSlice) => {
                let Value::Owner(mut node) = self.value(args.first()?)? else {
                    return None;
                };
                let length = property(span, node.memory.clone(), "length");
                let element = self.layouts.vector_element(&node.typ, span).ok()?;
                node.memory = with_root(
                    span,
                    node.memory,
                    contracts::multiply(span, length.clone(), contracts::literal(span, element)),
                    expr::integer(span, 0),
                    length,
                    self.layouts.owning_elements(&node.typ),
                );
                node.minima.remove(&vec![]);
                node.typ = value.typ.clone();
                Some(Value::Owner(node))
            }
            Some(ResourceIntrinsic::HeapDrop) => {
                self.value(args.first()?)?;
                Some(Value::Unit)
            }
            _ => self.checked_call(value, target, args),
        }
    }

    fn checked_call(&mut self, value: &Expr, target: &Fun, args: &Exprs) -> Option<Value> {
        let function = self.functions.get(target)?;
        let template = self.summaries.get(target)?.transfer.as_ref()?;
        self.appends |= template.appends;
        let mut values = HashMap::new();
        let mut locations = HashMap::new();
        for (index, (arg, parameter)) in args.iter().zip(function.x.params.iter()).enumerate() {
            if parameter.x.mode != Mode::Exec {
                continue;
            }
            let actual = if let Some(typ) = self.layouts.borrowed_owner(&parameter.x.typ) {
                let location = self.location(arg, typ)?;
                let node = self.get(&arg.span, &location, typ)?;
                locations.insert(index, location);
                Value::Owner(node)
            } else {
                self.value(arg)?
            };
            values.insert(index, actual);
        }
        let mut replacements = HashMap::new();
        for symbol in &template.symbols {
            let replacement = match (
                &symbol.input,
                values.get(&match &symbol.input {
                    Input::Scalar(i)
                    | Input::Forest(i)
                    | Input::Property(i, _, _)
                    | Input::Minimum(i, _) => *i,
                })?,
            ) {
                (Input::Scalar(_), Value::Scalar(value)) => value.clone(),
                (Input::Forest(_), Value::Owner(node)) => node.memory.clone(),
                (Input::Property(_, path, field), Value::Owner(node)) => {
                    let selected = expr::subtree(
                        &value.span,
                        node.memory.clone(),
                        expr::path(
                            &value.span,
                            path.iter().map(|slot| self.layouts.metadata_slot(slot)),
                        ),
                    );
                    property(&value.span, selected, field)
                }
                (Input::Minimum(_, path), Value::Owner(node)) => node
                    .minima
                    .get(path)
                    .map(|f| f.capacity.clone())
                    .unwrap_or_else(|| expr::integer(&value.span, 0)),
                _ => return None,
            };
            replacements.insert(symbol.name.clone(), replacement);
        }
        for (index, node) in &template.borrowed {
            self.set(&value.span, &locations[index], instantiate_node(node, &replacements))?;
        }
        Some(instantiate_value(&template.result, &replacements))
    }
}
