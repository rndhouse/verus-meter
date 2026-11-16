//! Recover executable synchronization transport and destruction from Rust MIR.
//!
//! Use drop-elaborated, unoptimized MIR: source last use and lexical declaration
//! order cannot substitute for executed destructors, especially for temporaries,
//! partial moves and early exits. This adapter does not interpret byte costs or
//! grant a memory proof. Unsupported effects remain explicit coverage obligations.

use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::{mir, ty};
use rustc_span::def_id::{DefId, LocalDefId};
use std::collections::HashMap;
use vir::ast::{Fun, ResourceIntrinsic};
use vir::messages::Span;
use vir::resource::memory::synchronization::flow::*;
use vir::resource::memory::synchronization::{LibraryType, Operation, Outcome};

pub(crate) fn lower<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    owner: LocalDefId,
    function: &dyn Fn(DefId) -> Fun,
    span: &dyn Fn(rustc_span::Span) -> Span,
) -> Graph {
    // Borrow rather than steal the compiler body; the ordinary borrow checker
    // and code generator must still consume their own query results.
    let body = tcx.mir_drops_elaborated_and_const_checked(owner).borrow();
    lower_body(tcx, &body, Some(owner), function, span)
}

/// Project a real compiler body, including generated FnOnce cleanup adapters.
pub(super) fn lower_body<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    owner: Option<LocalDefId>,
    function: &dyn Fn(DefId) -> Fun,
    span: &dyn Fn(rustc_span::Span) -> Span,
) -> Graph {
    let blocks = body
        .basic_blocks
        .iter()
        .map(|block| {
            let statements = block
                .statements
                .iter()
                .map(|statement| {
                    use mir::StatementKind as S;
                    let effect = match &statement.kind {
                        S::Assign(assignment) => {
                            let (target, value) = &**assignment;
                            match place(*target) {
                                Some(target) => Statement::Assign(target, rvalue(value)),
                                None => Statement::Unsupported,
                            }
                        }
                        S::StorageLive(local) => Statement::StorageLive(local.index()),
                        S::StorageDead(local) => Statement::StorageDead(local.index()),
                        S::SetDiscriminant { place: target, variant_index } => place(**target)
                            .map_or(Statement::Unsupported, |place| {
                                Statement::SetDiscriminant(place, variant_index.index())
                            }),
                        S::Nop | S::FakeRead(..) | S::PlaceMention(..) | S::AscribeUserType(..) => {
                            Statement::Nop
                        }
                        _ => Statement::Unsupported,
                    };
                    (span(statement.source_info.span), effect)
                })
                .collect();
            use mir::TerminatorKind as T;
            let terminator = block.terminator();
            let effect = match &terminator.kind {
                T::Goto { target } => Terminator::Goto(target.index()),
                T::SwitchInt { discr, targets } => Terminator::Switch {
                    operand: operand(discr),
                    targets: targets.iter().map(|(value, block)| (value, block.index())).collect(),
                    otherwise: targets.otherwise().index(),
                },
                T::Call { func, args, destination, target, unwind, .. } => {
                    match place(*destination) {
                        Some(result_place) => {
                            let call = match func.ty(&body.local_decls, tcx).kind() {
                                ty::FnDef(id, arguments) => {
                                    let arguments = arguments.skip_binder();
                                    let closure = arguments.types().next().and_then(|typ| {
                                        if let ty::Closure(closure, _) = typ.kind() {
                                            Some(*closure)
                                        } else {
                                            None
                                        }
                                    });
                                    let fn_trait = tcx.trait_of_assoc(*id);
                                    if let Some(closure) = closure
                                        && fn_trait.is_some()
                                        && [
                                            tcx.lang_items().fn_trait(),
                                            tcx.lang_items().fn_mut_trait(),
                                            tcx.lang_items().fn_once_trait(),
                                        ]
                                        .contains(&fn_trait)
                                    {
                                        Call::Closure(function(closure))
                                    } else {
                                        match super::intrinsics::call(tcx, *id, None, arguments) {
                                            Some(ResourceIntrinsic::Synchronization(operation)) => {
                                                Call::Primitive(operation)
                                            }
                                            Some(ResourceIntrinsic::Concurrency(operation)) => {
                                                Call::Concurrent(operation)
                                            }
                                            Some(ResourceIntrinsic::HeapDrop) => Call::Drop,
                                            _ => Call::Function(function(*id)),
                                        }
                                    }
                                }
                                _ => Call::Indirect,
                            };
                            let outcomes = if let Call::Primitive(operation) = call {
                                match acquisition_outcomes(
                                    tcx,
                                    operation,
                                    &result_place,
                                    destination_type(body, tcx, *destination),
                                ) {
                                    Some(outcomes) => outcomes,
                                    None => {
                                        return Block {
                                            statements,
                                            span: span(terminator.source_info.span),
                                            terminator: Terminator::Unsupported,
                                            cleanup: block.is_cleanup,
                                        };
                                    }
                                }
                            } else {
                                Vec::new()
                            };
                            Terminator::Call {
                                call,
                                arguments: args.iter().map(|arg| operand(&arg.node)).collect(),
                                destination: result_place,
                                outcomes,
                                next: target.map(|block| block.index()),
                                unwind: unwind_edge(*unwind),
                            }
                        }
                        None => Terminator::Unsupported,
                    }
                }
                T::Drop { place: target, target: next, unwind, drop: None, .. } => place(*target)
                    .map_or(Terminator::Unsupported, |place| Terminator::Drop {
                        place,
                        next: next.index(),
                        unwind: unwind_edge(*unwind),
                    }),
                T::Assert { cond, expected, target, unwind, .. } => Terminator::Assert {
                    condition: operand(cond),
                    expected: *expected,
                    next: target.index(),
                    unwind: unwind_edge(*unwind),
                },
                T::Return => Terminator::Return,
                T::UnwindResume | T::UnwindTerminate(..) => Terminator::Unwind,
                T::Unreachable => Terminator::Unreachable,
                _ => Terminator::Unsupported,
            };
            Block {
                statements,
                span: span(terminator.source_info.span),
                terminator: effect,
                cleanup: block.is_cleanup,
            }
        })
        .collect();
    Graph {
        blocks,
        bindings: owner.map(|owner| bindings(tcx, owner, body)).unwrap_or_default(),
        locals: body.local_decls.len(),
        arguments: body.arg_count,
    }
}

fn destination_type<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    destination: mir::Place<'tcx>,
) -> ty::Ty<'tcx> {
    destination.ty(&body.local_decls, tcx).ty
}

/// Read native wrapper field paths and discriminants from the pinned compiler.
/// The behavioral contract chooses which outcomes acquire; the Rust definitions
/// determine exactly where the corresponding guard lives in each result.
fn acquisition_outcomes<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    operation: Operation,
    destination: &Place,
    typ: ty::Ty<'tcx>,
) -> Option<Vec<AcquisitionOutcome>> {
    if operation.acquisition_contract().is_none() {
        return Some(Vec::new());
    }
    fn native<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        typ: ty::Ty<'tcx>,
        kind: LibraryType,
    ) -> Option<(ty::AdtDef<'tcx>, ty::GenericArgsRef<'tcx>)> {
        let ty::Adt(adt, args) = typ.kind() else { return None };
        (super::intrinsics::synchronization_type(tcx, adt.did()) == Some(kind))
            .then_some((*adt, *args))
    }
    fn field(place: &Place, index: usize) -> Place {
        let mut result = place.clone();
        result.projection.push(Projection::Field(index));
        result
    }
    fn variant<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        adt: ty::AdtDef<'tcx>,
        base: &Place,
        name: &str,
    ) -> Option<(&'tcx ty::VariantDef, Place, TagTest)> {
        let (index, variant) =
            adt.variants().iter_enumerated().find(|(_, variant)| variant.name.as_str() == name)?;
        let mut place = base.clone();
        place.projection.push(Projection::Variant(index.index()));
        Some((
            variant,
            place,
            TagTest {
                place: base.clone(),
                discriminant: adt.discriminant_for_variant(tcx, index).val,
            },
        ))
    }
    fn poison_guard<'tcx>(tcx: ty::TyCtxt<'tcx>, typ: ty::Ty<'tcx>, base: &Place) -> Option<Place> {
        let (poison, args) = native(tcx, typ, LibraryType::PoisonError)?;
        if !poison.is_struct() {
            return None;
        }
        let fields = &poison.non_enum_variant().fields;
        if fields.len() != 1 {
            return None;
        }
        native(
            tcx,
            fields.iter().next()?.ty(tcx, args).skip_normalization(),
            LibraryType::MutexGuard,
        )?;
        Some(field(base, 0))
    }

    let (result, args) = native(tcx, typ, LibraryType::Result)?;
    if !result.is_enum() || result.variants().len() != 2 {
        return None;
    }
    let (ok, ok_place, ok_test) = variant(tcx, result, destination, "Ok")?;
    let (err, err_place, err_test) = variant(tcx, result, destination, "Err")?;
    if ok.fields.len() != 1 || err.fields.len() != 1 {
        return None;
    }
    native(
        tcx,
        ok.fields.iter().next()?.ty(tcx, args).skip_normalization(),
        LibraryType::MutexGuard,
    )?;
    let mut outcomes = vec![AcquisitionOutcome {
        outcome: Outcome::Acquired,
        conditions: vec![ok_test],
        guard: Some(field(&ok_place, 0)),
    }];
    let error_typ = err.fields.iter().next()?.ty(tcx, args).skip_normalization();
    let error_place = field(&err_place, 0);
    if operation == Operation::MutexLock {
        outcomes.push(AcquisitionOutcome {
            outcome: Outcome::Poisoned,
            conditions: vec![err_test],
            guard: Some(poison_guard(tcx, error_typ, &error_place)?),
        });
    } else {
        let (error, error_args) = native(tcx, error_typ, LibraryType::TryLockError)?;
        if !error.is_enum() || error.variants().len() != 2 {
            return None;
        }
        let (poisoned, poison_place, poison_test) = variant(tcx, error, &error_place, "Poisoned")?;
        let (blocked, _, blocked_test) = variant(tcx, error, &error_place, "WouldBlock")?;
        if poisoned.fields.len() != 1 || !blocked.fields.is_empty() {
            return None;
        }
        let guard = poison_guard(
            tcx,
            poisoned.fields.iter().next()?.ty(tcx, error_args).skip_normalization(),
            &field(&poison_place, 0),
        )?;
        outcomes.push(AcquisitionOutcome {
            outcome: Outcome::Poisoned,
            conditions: vec![err_test.clone(), poison_test],
            guard: Some(guard),
        });
        outcomes.push(AcquisitionOutcome {
            outcome: Outcome::WouldBlock,
            conditions: vec![err_test, blocked_test],
            guard: None,
        });
    }
    Some(outcomes)
}

fn place(value: mir::Place<'_>) -> Option<Place> {
    let projection = value
        .projection
        .iter()
        .map(|projection| match projection {
            mir::ProjectionElem::Deref => Some(Projection::Deref),
            mir::ProjectionElem::Field(field, _) => Some(Projection::Field(field.index())),
            mir::ProjectionElem::Downcast(_, variant) => Some(Projection::Variant(variant.index())),
            _ => None,
        })
        .collect::<Option<_>>()?;
    Some(Place { local: value.local.index(), projection })
}

fn operand(value: &mir::Operand<'_>) -> Operand {
    match value {
        mir::Operand::Move(source) => place(*source).map_or(Operand::Unsupported, Operand::Move),
        mir::Operand::Copy(source) => place(*source).map_or(Operand::Unsupported, Operand::Copy),
        mir::Operand::Constant(value) => value
            .const_
            .try_to_scalar_int()
            .map(|value| Operand::Scalar(value.to_bits(value.size())))
            .unwrap_or(Operand::Constant),
        _ => Operand::Unsupported,
    }
}

fn rvalue(value: &mir::Rvalue<'_>) -> Value {
    use mir::Rvalue as R;
    match value {
        R::Use(source, _) => Value::Use(operand(source)),
        R::Ref(_, _, source) => place(*source).map_or(Value::Unsupported, Value::Borrow),
        R::CopyForDeref(source) => place(*source)
            .map(|place| Value::Use(Operand::Copy(place)))
            .unwrap_or(Value::Unsupported),
        R::Discriminant(source) => place(*source).map_or(Value::Unsupported, Value::Discriminant),
        R::Aggregate(kind, fields) => {
            let variant = match &**kind {
                mir::AggregateKind::Tuple => None,
                mir::AggregateKind::Adt(_, variant, _, _, None) => Some(variant.index()),
                _ => return Value::Unsupported,
            };
            Value::Aggregate { variant, fields: fields.iter().map(operand).collect() }
        }
        R::BinaryOp(..) | R::UnaryOp(..) => Value::Other,
        _ => Value::Unsupported,
    }
}

fn unwind_edge(value: mir::UnwindAction) -> Unwind {
    match value {
        mir::UnwindAction::Cleanup(block) => Unwind::Cleanup(block.index()),
        _ => Unwind::Exit,
    }
}

/// MIR debug bindings retain exact source spans before optimization. Match both
/// name and span, including hygiene; ambiguous matches deliberately stay absent.
/// Do not reconstruct shadowing or macro identity from printed variable names.
fn bindings<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &mir::Body<'tcx>,
) -> HashMap<vir::ast::VarIdent, SourceBinding> {
    struct Bindings {
        source: Vec<(rustc_span::Symbol, rustc_span::Span, vir::ast::VarIdent)>,
    }
    impl<'tcx> Visitor<'tcx> for Bindings {
        fn visit_pat(&mut self, pattern: &'tcx rustc_hir::Pat<'tcx>) {
            if let rustc_hir::PatKind::Binding(_, id, ident, _) = pattern.kind {
                self.source.push((
                    ident.name,
                    pattern.span,
                    crate::rust_to_vir_base::local_to_var(&ident, id.local_id),
                ));
            }
            intravisit::walk_pat(self, pattern);
        }
    }
    let mut bindings = Bindings { source: Vec::new() };
    bindings.visit_body(tcx.hir_body_owned_by(owner));
    let mut matched = HashMap::<_, Vec<_>>::new();
    for debug in &body.var_debug_info {
        if debug.composite.is_some() {
            // A debug fragment does not identify the whole source binding.
            continue;
        }
        let mir::VarDebugInfoContents::Place(source) = debug.value else { continue };
        for (name, span, variable) in &bindings.source {
            if debug.name == *name
                && debug.source_info.span == *span
                && let Some(place) = place(source)
            {
                matched.entry(variable.clone()).or_default().push(place);
            }
        }
    }
    matched
        .into_iter()
        .filter_map(|(variable, mut places)| {
            places.dedup();
            (places.len() == 1)
                .then(|| (variable, SourceBinding { place: places.pop().unwrap(), mode: None }))
        })
        .collect()
}

#[cfg(test)]
mod tests;
