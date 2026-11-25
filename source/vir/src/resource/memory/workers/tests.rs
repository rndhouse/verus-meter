//! Storage transitions use the same executable constructors and capture mover as
//! body accounting. Checked body summaries and native Result matching are later
//! adapters; these tests do not install an assumed worker memory allowance.

use super::*;
use crate::resource::memory::{
    accounting::Accounting,
    concurrency::{Capture, CaptureMode, Closure, Evidence, Operation},
    heap::OwnerSlot,
    layout::Layouts,
    lifetime::Value,
    synchronization::{LibraryType, LibraryTypes, flow},
};
use std::{collections::HashMap, sync::Arc};

fn span(id: u64) -> Span {
    Span { raw_span: Arc::new(()), id, data: Arc::new([]), as_string: "worker storage test".into() }
}

fn decorated(decoration: TypDecoration, inner: Typ) -> Typ {
    Arc::new(TypX::Decorate(
        decoration,
        Some(TypDecorationArg {
            allocator_typ: Arc::new(TypX::Primitive(Primitive::Global, Arc::new(vec![]))),
        }),
        inner,
    ))
}

fn call(site: &Span, typ: &Typ, intrinsic: ResourceIntrinsic, args: Vec<Expr>) -> Expr {
    let types = if intrinsic == ResourceIntrinsic::HeapDrop {
        args.iter().map(|argument| argument.typ.clone()).collect()
    } else {
        vec![]
    };
    SpannedTyped::new(
        site,
        typ,
        ExprX::Call {
            target: CallTarget::Fun(
                CallTargetKind::Static,
                crate::fun!(CrateId::Internal => "worker_test"; "operation"),
                Arc::new(types),
                Arc::new(vec![]),
                CallTargetAttrs {
                    autospec: AutospecUsage::Final,
                    const_var: false,
                    assume_external_allowed: false,
                    resource_intrinsic: Some(intrinsic),
                },
            ),
            args: Arc::new(args),
            post_args: None,
            body: None,
        },
    )
}

/// Inspect the descriptor emitted for an actual constructor's owner. The
/// verified forest algebra checks transport; this checks the compiler bridge
/// supplies the canonical identity rather than dropping it into byte-only data.
fn assert_reference(
    analysis: &mut Analysis<'_>,
    owner: &Owner,
    operation: &str,
    identity: &[i128],
) {
    use crate::resource::memory::{metadata::expr, transfer::simplify::inspect::same_expression};
    let site = span(900);
    let before = analysis.storage.live();
    let records = analysis.call_metadata(&site, owner, &mut vec![]).unwrap();
    let mut found = 0;
    crate::ast_visitor::expr_visitor_check(&records, &mut |_, value| {
        if let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &value.x
            && expr::is_operation(function, operation)
        {
            found += 1;
            assert!(same_expression(&args[1], &expr::path(&site, identity.iter().copied())));
        }
        Ok::<_, ()>(())
    })
    .unwrap();
    assert_eq!(found, 1);
    assert_eq!(analysis.storage.live(), before);
}

#[test]
fn executable_handle_drop_retains_the_worker_and_its_capture_allocation() {
    let site = span(1);
    let initializer = source_box(&site);
    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let (info, expression) = closure(1, Some((source.clone(), initializer.typ.clone())));
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let value = analysis.produce(&initializer).unwrap();
        analysis.var_modes.insert(source.clone(), Mode::Exec);
        analysis.slots.insert(source.clone(), value);
        analysis.heap.owners.insert(source, analysis.result_owner.take().unwrap());
        let typ = Arc::new(TypX::Datatype(
            handle.clone(),
            Arc::new(vec![initializer.typ.clone()]),
            Arc::new(vec![]),
        ));
        let spawn = call(
            &span(10),
            &typ,
            ResourceIntrinsic::Concurrency(Operation::StdSpawn),
            vec![expression],
        );
        let value = analysis.fresh_value(&spawn.span, &spawn.typ).unwrap();
        let owner = analysis.publish_owner(&spawn).unwrap().unwrap();
        assert_reference(
            analysis,
            &owner,
            "worker_reference",
            &owner.worker.as_ref().unwrap().actor.descriptor(),
        );
        let name = VarIdent(Arc::new("handle".into()), VarIdentDisambiguate::RustcId(2));
        analysis.var_modes.insert(name.clone(), Mode::Exec);
        analysis.slots.insert(name.clone(), value);
        analysis.heap.owners.insert(name.clone(), owner);
        let argument = SpannedTyped::new(
            &span(11),
            &typ,
            ExprX::ReadPlace(
                SpannedTyped::new(&span(11), &typ, PlaceX::Local(name.clone())),
                UnfinalizedReadKind {
                    preliminary_kind: ReadKind::Move(MoveExecToProofOkay::No),
                    id: 0,
                },
            ),
        );
        analysis
            .discard(&call(
                &span(12),
                &crate::ast_util::unit_typ(),
                ResourceIntrinsic::HeapDrop,
                vec![argument],
            ))
            .unwrap();
        assert!(!analysis.slots.contains_key(&name));
        assert_eq!(analysis.storage.live(), 73); // only the handle's eight bytes ended
        assert!(analysis.heap.workers.check_closed(&span(13)).is_err());
    });
}

#[test]
fn repeated_publications_at_one_site_have_distinct_worker_identities() {
    let (info, expression) = closure(1, None);
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let (first, first_handle) = spawn(analysis, handle, expression.clone(), 10);
        let (second, second_handle) = spawn(analysis, handle, expression, 10);
        assert_ne!(first, second);
        assert_eq!(first.descriptor()[0], second.descriptor()[0]);
        assert_ne!(first.descriptor()[1], second.descriptor()[1]);
        assert_ne!(
            analysis.heap.workers.records[&first].completion,
            analysis.heap.workers.records[&second].completion,
        );
        assert_eq!(analysis.heap.workers.records.len(), 2);
        assert_eq!(analysis.storage.live(), 18);
        for (id, handle) in [(first, first_handle), (second, second_handle)] {
            let frame = analysis.heap.workers.enter(id, &span(11)).unwrap().storage;
            if let Some(owner) = frame.owner {
                analysis.release_owner(owner, &span(11));
            }
            analysis.release_value(frame.value, &span(11));
            analysis
                .heap
                .workers
                .transition_completion(
                    id,
                    &span(12),
                    Storage { typ: crate::ast_util::unit_typ(), value: Value::unit(), owner: None },
                )
                .unwrap();
            finish_join(analysis, id, handle);
            assert!(analysis.collect_worker_result(id, &span(13)).is_err());
            assert_eq!(analysis.storage.live(), if id == first { 9 } else { 0 });
        }
        assert_eq!(analysis.storage.live(), 0);
        analysis.heap.workers.check_closed(&span(14)).unwrap();
    });
}

#[test]
fn child_families_preserve_the_enclosing_worker_occurrence() {
    let (parent, parent_expression) = closure(1, None);
    let (child, child_expression) = closure(2, None);
    let mut evidence = Evidence::default();
    evidence.closures.insert(parent.id, parent);
    evidence.closures.insert(child.id, child);
    with_analysis(&evidence, |analysis, handle| {
        let (first, first_handle) = spawn(analysis, handle, parent_expression.clone(), 10);
        let (second, second_handle) = spawn(analysis, handle, parent_expression, 10);
        for parent in [first, second] {
            let frame = analysis.heap.workers.enter(parent, &span(11)).unwrap().storage;
            if let Some(owner) = frame.owner {
                analysis.release_owner(owner, &span(11));
            }
            analysis.release_value(frame.value, &span(11));
        }
        analysis.current_worker = Some(first);
        let (first_child, first_child_handle) =
            spawn(analysis, handle, child_expression.clone(), 12);
        analysis.current_worker = Some(second);
        let (second_child, second_child_handle) = spawn(analysis, handle, child_expression, 12);
        assert_ne!(first_child.descriptor()[0], second_child.descriptor()[0]);
        for (child, handle) in
            [(first_child, first_child_handle), (second_child, second_child_handle)]
        {
            let frame = analysis.heap.workers.enter(child, &span(13)).unwrap().storage;
            if let Some(owner) = frame.owner {
                analysis.release_owner(owner, &span(13));
            }
            analysis.release_value(frame.value, &span(13));
            analysis.heap.workers.transition_completion(child, &span(14), empty_result()).unwrap();
            finish_join(analysis, child, handle);
        }
        analysis.current_worker = None;
        for (parent, handle) in [(first, first_handle), (second, second_handle)] {
            analysis.heap.workers.transition_completion(parent, &span(15), empty_result()).unwrap();
            finish_join(analysis, parent, handle);
        }
        analysis.current_worker = None;
        analysis.heap.workers.check_closed(&span(16)).unwrap();
        assert_eq!(analysis.storage.live(), 0);
    });
}

fn empty_result() -> Storage {
    Storage { typ: crate::ast_util::unit_typ(), value: Value::unit(), owner: None }
}

#[test]
fn moved_worker_definitions_restore_native_body_effects_exactly_once() {
    let source = VarIdent(Arc::new("shared".into()), VarIdentDisambiguate::RustcId(1));
    let typ = decorated(TypDecoration::Arc, Arc::new(TypX::Int(IntRange::U(64))));
    let (info, mut expression) = closure(1, Some((source, typ.clone())));
    let ExprX::NonSpecClosure { body, .. } = &mut Arc::make_mut(&mut expression).x else {
        unreachable!()
    };
    *body = SpannedTyped::new(&span(200), &body.typ, body.x.clone());
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    evidence.erased_operations.insert(
        200,
        vec![crate::resource::memory::concurrency::ErasedOperation {
            function: crate::fun!(CrateId::Internal => "worker_test"; "clone"),
            operation: Operation::ArcClone,
            result: typ,
            span: span(201),
            receiver_scope: None,
        }],
    );
    let moved = SpannedTyped::new(
        &span(202),
        &expression.typ,
        ExprX::ReadPlace(
            SpannedTyped::new(
                &span(202),
                &expression.typ,
                PlaceX::Local(VarIdent(Arc::new("moved".into()), VarIdentDisambiguate::RustcId(2))),
            ),
            UnfinalizedReadKind {
                preliminary_kind: ReadKind::Move(MoveExecToProofOkay::No),
                id: 0,
            },
        ),
    );
    let restored = body::definition(&moved, &evidence, std::iter::once(&expression)).unwrap();
    let direct = body::definition(&restored, &evidence, std::iter::empty()).unwrap();
    let clones = |expression: &Expr| {
        let mut count = 0;
        crate::ast_visitor::expr_visitor_check(expression, &mut |_, value| {
            if matches!(&value.x, ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. }
                if attrs.resource_intrinsic == Some(ResourceIntrinsic::Concurrency(Operation::ArcClone)))
            {
                count += 1;
            }
            Ok::<(), ()>(())
        }).unwrap();
        count
    };
    assert_eq!(clones(&expression), 0);
    assert_eq!(clones(&restored), 1);
    assert_eq!(clones(&direct), 1);
    assert!(body::definition(&moved, &evidence, std::iter::empty()).is_err());
    assert!(body::definition(&moved, &evidence, [&expression, &expression].into_iter()).is_err());
}

#[test]
fn worker_entry_checks_capture_coverage_and_native_cleanup() {
    let site = span(1);
    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let initializer = source_box(&site);
    let (info, expression) = closure(1, Some((source.clone(), initializer.typ.clone())));
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, _| {
        let value = analysis.produce(&initializer).unwrap();
        analysis.var_modes.insert(source.clone(), Mode::Exec);
        analysis.slots.insert(source.clone(), value);
        analysis.heap.owners.insert(source, analysis.result_owner.take().unwrap());
        let value = analysis.produce(&expression).unwrap();
        let owner = analysis.result_owner.take();
        let storage = Storage { typ: expression.typ.clone(), value, owner };
        assert!(
            body::Entry::checked(
                expression.clone(),
                storage.clone(),
                &evidence,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_ok()
        );
        let mut missing = storage.clone();
        missing.owner.as_mut().unwrap().children.remove(&OwnerSlot::Capture(0));
        assert!(
            body::Entry::checked(
                expression.clone(),
                missing,
                &evidence,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_err()
        );
        let mut missing_projection = evidence.clone();
        missing_projection.closures.get_mut(&1).unwrap().captures[0].body_place = None;
        assert!(
            body::Entry::checked(
                expression.clone(),
                storage.clone(),
                &missing_projection,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_err()
        );
        let mut callable = expression.clone();
        let TypX::AnonymousClosure(arguments, result, _, id) = &*expression.typ else {
            unreachable!()
        };
        Arc::make_mut(&mut callable).typ = Arc::new(TypX::AnonymousClosure(
            arguments.clone(),
            result.clone(),
            ClosureKind::Fn,
            *id,
        ));
        let mut environment = storage;
        environment.typ = callable.typ.clone();
        assert!(
            body::Entry::checked(
                callable,
                environment,
                &evidence,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_err()
        );
    });
}

#[test]
fn scalar_capture_observations_survive_parent_mutation_and_closure_copies() {
    use crate::resource::memory::transfer::simplify::inspect::same_expression;

    let source = VarIdent(Arc::new("size".into()), VarIdentDisambiguate::RustcId(1));
    let binding = VarIdent(Arc::new("worker".into()), VarIdentDisambiguate::RustcId(2));
    let scalar = Arc::new(TypX::Int(IntRange::U(16)));
    let (mut info, expression) = closure(1, Some((source.clone(), scalar.clone())));
    info.captures[0].mode = CaptureMode::Copy;
    let captures = info.captures.clone();
    let (mut outer, outer_expression) = closure(2, Some((binding.clone(), expression.typ.clone())));
    outer.captures[0].mode = CaptureMode::Copy;
    let outer_captures = outer.captures.clone();
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    evidence.closures.insert(outer.id, outer);
    with_analysis(&evidence, |analysis, _| {
        let original = analysis.fresh_value(&span(1), &scalar).unwrap();
        analysis.var_modes.insert(source.clone(), Mode::Exec);
        analysis.slots.insert(source.clone(), original);
        let value = analysis.produce(&expression).unwrap();
        let environment = value.environment.unwrap();
        assert!(analysis.growth.environments.matches(environment, 1, &captures));
        let captured = analysis.growth.environments.scalar(environment, 0).unwrap().clone();
        assert!(crate::ast_util::types_equal(&captured.typ, &scalar));
        let [snapshot] = analysis.growth.before[&expression.span.id].as_slice() else {
            panic!("one scalar snapshot at construction");
        };
        let StmtX::Expr(snapshot) = &snapshot.x else { unreachable!() };
        let ExprX::Assign { rhs, typ, .. } = &snapshot.x else { unreachable!() };
        let ExprX::ReadPlace(place, kind) = &rhs.x else { unreachable!() };
        assert!(matches!(&place.x, PlaceX::Local(name) if *name == source));
        assert!(matches!(kind.preliminary_kind, ReadKind::Spec));
        assert!(crate::ast_util::types_equal(typ, &scalar));

        // Executable parent mutation occurs after construction. Neither a copy
        // nor worker entry may replace the retained input with this new value.
        let mutation = super::super::symbolic::assign(
            &span(3),
            &SpannedTyped::new(&span(3), &scalar, ExprX::Var(source.clone())),
            SpannedTyped::new(&span(3), &scalar, ExprX::Const(Constant::Int(0.into()))),
        );
        let StmtX::Expr(mutation) = &mutation.x else { unreachable!() };
        analysis.discard(mutation).unwrap();
        analysis.var_modes.insert(binding.clone(), Mode::Exec);
        analysis.slots.insert(binding.clone(), value.clone());
        let copied = analysis
            .produce_place(
                &SpannedTyped::new(&span(4), &expression.typ, PlaceX::Local(binding.clone())),
                &expression.typ,
                true,
                &span(4),
            )
            .unwrap();
        assert!(copied.environment == value.environment);
        assert_ne!(copied.ids, value.ids);
        assert!(same_expression(
            analysis.growth.environments.scalar(copied.environment.unwrap(), 0).unwrap(),
            &captured,
        ));
        let outer = analysis.produce(&outer_expression).unwrap();
        assert!(analysis.growth.environments.matches(
            outer.environment.unwrap(),
            2,
            &outer_captures,
        ));
        let mut storage = Storage { typ: expression.typ.clone(), value: copied, owner: None };
        assert!(
            body::Entry::checked(
                expression.clone(),
                storage.clone(),
                &evidence,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_ok()
        );
        storage.value.environment = None;
        assert!(
            body::Entry::checked(
                expression.clone(),
                storage,
                &evidence,
                analysis.layouts,
                &analysis.growth.environments,
                &analysis.heap.shared,
            )
            .is_err()
        );
        // A representative loop visit is not an immutable captured input for
        // every outstanding worker. Admission waits for occurrence lifting.
        analysis.growth.loop_depth = 1;
        let repeated = analysis.produce(&expression).unwrap();
        analysis.growth.loop_depth = 0;
        let repeated_id = repeated.environment.unwrap();
        assert!(!analysis.growth.environments.matches(repeated_id, 1, &captures));
        assert!(analysis.growth.environments.scalar(repeated_id, 0).is_none());
        analysis.slots.insert(binding, repeated);
        let wrapped = analysis.produce(&outer_expression).unwrap();
        assert!(!analysis.growth.environments.matches(
            wrapped.environment.unwrap(),
            2,
            &outer_captures,
        ));
    });
}

#[test]
fn capture_views_preserve_dereference_paths_and_reject_overlapping_bindings() {
    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let scalar = Arc::new(TypX::Int(IntRange::U(64)));
    let typ = decorated(TypDecoration::Box, scalar.clone());
    let (mut info, _) = closure(1, Some((source.clone(), typ)));
    let layouts = Layouts::new(&[], None, None, None);
    let views = captures::Captures::new(&info, &layouts, &span(1)).unwrap();
    assert!(
        views.source_path(&(source.clone(), vec![OwnerSlot::Contents]))
            == Some(vec![OwnerSlot::Capture(0), OwnerSlot::Contents]),
    );
    let whole = info.captures[0].clone();
    let mut inner = whole.clone();
    inner.projection.push(flow::Projection::Deref);
    inner.typ = scalar;
    inner.mode = CaptureMode::Copy;
    info.captures = vec![inner.clone()];
    let views = captures::Captures::new(&info, &layouts, &span(2)).unwrap();
    assert!(views.source_path(&(source.clone(), vec![])).is_none());
    assert!(
        views.source_path(&(source.clone(), vec![OwnerSlot::Contents]))
            == Some(vec![OwnerSlot::Capture(0)]),
    );
    assert!(views.owned_slots(&layouts).is_empty());
    inner.body_place.as_mut().unwrap().projection = vec![flow::Projection::Field(1)];
    info.captures = vec![whole.clone(), inner];
    assert!(captures::Captures::new(&info, &layouts, &span(3)).is_err());
    let mut other = whole.clone();
    other.source = VarIdent(Arc::new("other".into()), VarIdentDisambiguate::RustcId(2));
    info.captures = vec![whole, other];
    assert!(captures::Captures::new(&info, &layouts, &span(4)).is_err());
    info.captures[1].body_place.as_mut().unwrap().projection = vec![flow::Projection::Field(1)];
    assert!(captures::Captures::new(&info, &layouts, &span(5)).is_ok());
}

fn unit(site: &Span) -> Expr {
    SpannedTyped::new(site, &crate::ast_util::unit_typ(), ExprX::Block(Arc::new(vec![]), None))
}

fn source_box(site: &Span) -> Expr {
    let byte = Arc::new(TypX::Int(IntRange::U(8)));
    let payload = Arc::new(TypX::Primitive(
        Primitive::Array,
        Arc::new(vec![byte.clone(), Arc::new(TypX::ConstInt(64.into()))]),
    ));
    let zero = SpannedTyped::new(site, &byte, ExprX::Const(Constant::Int(0.into())));
    let array = call(site, &payload, ResourceIntrinsic::ArrayRepeat, vec![zero]);
    call(site, &decorated(TypDecoration::Box, payload), ResourceIntrinsic::BoxNew, vec![array])
}

fn closure(id: usize, capture: Option<(VarIdent, Typ)>) -> (Closure, Expr) {
    let site = span(100 + id as u64);
    let result =
        capture.as_ref().map(|(_, typ)| typ.clone()).unwrap_or_else(crate::ast_util::unit_typ);
    let body = if let Some((name, typ)) = &capture {
        SpannedTyped::new(
            &site,
            typ,
            ExprX::ReadPlace(
                SpannedTyped::new(&site, typ, PlaceX::Local(name.clone())),
                UnfinalizedReadKind {
                    preliminary_kind: ReadKind::Move(MoveExecToProofOkay::No),
                    id: 0,
                },
            ),
        )
    } else {
        unit(&site)
    };
    let captures = capture
        .into_iter()
        .map(|(source, typ)| Capture {
            source,
            source_typ: typ.clone(),
            typ,
            projection: vec![],
            mode: CaptureMode::Move,
            body_place: Some(flow::Place {
                local: 1,
                projection: vec![flow::Projection::Field(0)],
            }),
        })
        .collect();
    let info = Closure {
        id,
        function: crate::fun!(CrateId::Internal => "worker_test"; "body"),
        kind: ClosureKind::FnOnce,
        span: site.clone(),
        captures,
        by_move: true,
        copy: false,
        body: flow::Graph {
            blocks: vec![flow::Block {
                statements: vec![],
                span: site.clone(),
                terminator: flow::Terminator::Return,
                cleanup: false,
            }],
            bindings: HashMap::new(),
            locals: 2,
            arguments: 1,
        },
    };
    let typ =
        Arc::new(TypX::AnonymousClosure(Arc::new(vec![]), result.clone(), ClosureKind::FnOnce, id));
    let expression = SpannedTyped::new(
        &site,
        &typ,
        ExprX::NonSpecClosure {
            params: Arc::new(vec![]),
            proof_fn_modes: None,
            body,
            requires: Arc::new(vec![]),
            ensures: Arc::new(vec![]),
            mask_spec: None,
            ret: Arc::new(VarBinderX {
                name: VarIdent(Arc::new("result".into()), VarIdentDisambiguate::RustcId(9)),
                a: result,
            }),
            external_spec: None,
        },
    );
    (info, expression)
}

fn with_analysis(evidence: &Evidence, run: impl FnOnce(&mut Analysis<'_>, &Dt)) {
    let handle =
        Dt::Path(crate::fun!(CrateId::Internal => "worker_test"; "JoinHandle").path.clone());
    let types: LibraryTypes = [(handle.clone(), LibraryType::StdJoinHandle)].into_iter().collect();
    let layouts = Layouts::new(&[], None, None, None)
        .with_synchronization_types(&types)
        .with_closures(evidence);
    let functions = HashMap::new();
    let summaries = HashMap::new();
    let budgets = HashMap::new();
    let site = span(0);
    let mut analysis = Analysis {
        fresh_span: &|_| unreachable!("this test has no protocol witness"),
        worker_inputs: vec![],
        capture_views: Default::default(),
        evaluations: Default::default(),
        concurrency: evidence,
        current_worker: None,
        section_scopes: Vec::new(),
        flow: Default::default(),
        transitions: Default::default(),
        slots: HashMap::new(),
        produced: None,
        summaries: &summaries,
        result_owner: None,
        budgets: &budgets,
        layouts: &layouts,
        functions: &functions,
        var_modes: HashMap::new(),
        storage: Accounting::new(&site, 4096),
        calls: vec![],
        checkpoints: vec![],
        stable_scalars: Default::default(),
        heap: Default::default(),
        obligations: vec![],
        checks: vec![],
        input_paths: vec![],
        growth: Default::default(),
        bound: super::super::contracts::literal(&site, 4096),
    };
    run(&mut analysis, &handle);
}

fn spawn(
    analysis: &mut Analysis<'_>,
    handle: &Dt,
    expression: Expr,
    site: u64,
) -> (WorkerId, Value) {
    let TypX::AnonymousClosure(_, result, _, _) = &*expression.typ else { unreachable!() };
    let typ =
        Arc::new(TypX::Datatype(handle.clone(), Arc::new(vec![result.clone()]), Arc::new(vec![])));
    let expression = call(
        &span(site),
        &typ,
        ResourceIntrinsic::Concurrency(Operation::StdSpawn),
        vec![expression],
    );
    let value = analysis.fresh_value(&expression.span, &expression.typ).unwrap();
    let owner = analysis.publish_owner(&expression).unwrap().unwrap();
    (owner.worker.unwrap().actor, value)
}

fn finish_join(analysis: &mut Analysis<'_>, id: WorkerId, value: Value) -> Storage {
    let site = span(40);
    analysis.heap.workers.wait(id, analysis.current_worker, &site, value).unwrap();
    analysis.collect_worker_result(id, &site).unwrap()
}

#[test]
fn capture_and_result_ownership_survive_publication_completion_and_join() {
    let site = span(1);
    let initializer = source_box(&site);
    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let (info, expression) = closure(1, Some((source.clone(), initializer.typ.clone())));
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let value = analysis.produce(&initializer).unwrap();
        analysis.var_modes.insert(source.clone(), Mode::Exec);
        analysis.slots.insert(source.clone(), value);
        analysis.heap.owners.insert(source.clone(), analysis.result_owner.take().unwrap());
        assert_eq!(analysis.storage.live(), 72);
        let (id, handle_value) = spawn(analysis, handle, expression, 10);
        assert!(!analysis.slots.contains_key(&source));
        assert_eq!(analysis.storage.live(), 81); // backing + capture + handle + tag
        let mut entry = analysis.heap.workers.enter(id, &site).unwrap();
        assert!(
            analysis.heap.workers.complete(id, &site).is_err(),
            "a ledger entry alone is not checked executable completion"
        );
        let ExprX::NonSpecClosure { body, .. } = &entry.definition.x else {
            panic!("worker definition")
        };
        assert!(
            matches!(&body.x, ExprX::ReadPlace(place, _) if matches!(&place.x, PlaceX::Local(name) if name == &source))
        );
        let payload = entry.take_capture_owner(&(source.clone(), vec![])).unwrap();
        assert!(entry.take_capture_owner(&(source, vec![])).is_err());
        let mut frame = entry.into_return_cleanup(analysis.layouts).unwrap();
        let environment = frame.owner.take().unwrap();
        analysis.release_owner(environment, &site);
        let result =
            Storage { typ: initializer.typ.clone(), value: frame.value, owner: Some(payload) };
        analysis.heap.workers.transition_completion(id, &site, result).unwrap();
        assert_eq!(analysis.storage.live(), 81); // completion has not collected the result
        assert!(analysis.heap.workers.check_closed(&site).is_err());
        let result = finish_join(analysis, id, handle_value);
        assert_eq!(analysis.storage.live(), 72); // same allocation transferred, not recreated
        analysis.heap.workers.check_closed(&site).unwrap();
        analysis.release_owner(result.owner.unwrap(), &site);
        analysis.release_value(result.value, &site);
        assert_eq!(analysis.storage.live(), 0);
        assert_eq!(analysis.storage.peak().bytes, 81);
    });
}

/// Exercise the invocation boundary using the same Box/closure constructors as
/// accounting. These are boundary checks, not a substitute for body verification.
#[test]
fn normal_return_requires_body_cleanup_or_retains_the_borrowed_environment() {
    use crate::resource::memory::concurrency::invocation::Invocation;

    for kind in [ClosureKind::FnOnce, ClosureKind::Fn, ClosureKind::FnMut] {
        let site = span(1);
        let initializer = source_box(&site);
        let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
        let (mut info, mut expression) =
            closure(1, Some((source.clone(), initializer.typ.clone())));
        info.kind = kind;
        if kind != ClosureKind::FnOnce {
            info.captures[0]
                .body_place
                .as_mut()
                .unwrap()
                .projection
                .insert(0, flow::Projection::Deref);
        }
        // Borrowed bodies retain their Box and produce unit. Owned-body cleanup
        // is applied explicitly below; none of these synthetic bodies is a proof.
        Arc::make_mut(&mut expression).typ = Arc::new(TypX::AnonymousClosure(
            Arc::new(vec![]),
            crate::ast_util::unit_typ(),
            kind,
            1,
        ));
        let ExprX::NonSpecClosure { body, ret, .. } = &mut Arc::make_mut(&mut expression).x else {
            unreachable!()
        };
        *body = unit(&site);
        Arc::make_mut(ret).a = crate::ast_util::unit_typ();
        let mut evidence = Evidence::default();
        evidence.closures.insert(info.id, info);
        with_analysis(&evidence, |analysis, _| {
            let value = analysis.produce(&initializer).unwrap();
            analysis.var_modes.insert(source.clone(), Mode::Exec);
            analysis.slots.insert(source.clone(), value);
            analysis.heap.owners.insert(source.clone(), analysis.result_owner.take().unwrap());
            let value = analysis.produce(&expression).unwrap();
            let storage =
                Storage { typ: expression.typ.clone(), value, owner: analysis.result_owner.take() };
            let entry = |storage| {
                body::Entry::checked(
                    expression.clone(),
                    storage,
                    &evidence,
                    analysis.layouts,
                    &analysis.growth.environments,
                    &analysis.heap.shared,
                )
                .unwrap()
            };
            let mut valid = entry(storage.clone());
            if kind == ClosureKind::FnOnce {
                assert_eq!(valid.invocation, Invocation::OwnedBody);
                assert!(entry(storage).into_return_cleanup(analysis.layouts).is_err());
                let owner = valid.take_capture_owner(&(source.clone(), vec![])).unwrap();
                assert!(valid.take_capture_owner(&(source.clone(), vec![])).is_err());
                analysis.release_owner(owner, &site);
                assert_eq!(analysis.storage.live(), 8);
            } else {
                assert!(valid.invocation.cleans_up_after_body());
                assert!(valid.take_capture_owner(&(source.clone(), vec![])).is_err());
                let mut missing = entry(storage);
                missing.storage.owner.as_mut().unwrap().children.clear();
                assert!(missing.into_return_cleanup(analysis.layouts).is_err());
                assert_eq!(analysis.storage.live(), 72);
            }
            let cleanup = valid.into_return_cleanup(analysis.layouts).unwrap();
            // A return description does not release anything by itself.
            assert_eq!(analysis.storage.live(), if kind == ClosureKind::FnOnce { 8 } else { 72 });
            analysis.release_owner(cleanup.owner.unwrap(), &site);
            analysis.release_value(cleanup.value, &site);
            assert_eq!(analysis.storage.live(), 0);
        });
    }
}

#[test]
fn invocation_requires_receiver_evidence_without_matching_body_control_flow() {
    use crate::resource::memory::concurrency::invocation::Invocation;

    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let (mut info, _) = closure(1, Some((source, source_box(&span(1)).typ.clone())));
    info.kind = ClosureKind::Fn;
    let check = |info: &Closure| Invocation::checked(info, &info.span);
    assert!(check(&info).is_err()); // shared body requires a borrowed receiver view
    info.captures[0].body_place.as_mut().unwrap().projection.insert(0, flow::Projection::Deref);
    assert_eq!(check(&info).unwrap(), Invocation::SharedBody);
    // Unwind/unsupported paths remain evidence for the subsequent body checker,
    // never assumed absent because the invocation boundary is well formed.
    info.body.blocks[0].terminator = flow::Terminator::Unsupported;
    info.body.blocks.push(flow::Block {
        statements: vec![],
        span: span(2),
        terminator: flow::Terminator::Unwind,
        cleanup: true,
    });
    assert_eq!(check(&info).unwrap(), Invocation::SharedBody);
    info.body.arguments = 2;
    assert!(check(&info).is_err());
    info.body.arguments = 1;
    info.captures[0].body_place.as_mut().unwrap().local = 0;
    assert!(check(&info).is_err());
    info.captures[0].body_place = None;
    assert!(check(&info).is_err());
}

#[test]
fn shared_capture_and_completed_result_retain_one_canonical_payload() {
    let site = span(1);
    let initializer = source_box(&site);
    let typ = decorated(TypDecoration::Arc, initializer.typ.clone());
    let root = VarIdent(Arc::new("root".into()), VarIdentDisambiguate::RustcId(1));
    let copy = VarIdent(Arc::new("copy".into()), VarIdentDisambiguate::RustcId(2));
    let (info, expression) = closure(1, Some((copy.clone(), typ.clone())));
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let value = analysis
            .produce(&call(
                &site,
                &typ,
                ResourceIntrinsic::Concurrency(Operation::ArcNew),
                vec![initializer],
            ))
            .unwrap();
        let owner = analysis.result_owner.take().unwrap();
        let identity = owner.shared;
        let root_id = identity.unwrap().known().unwrap();
        assert_reference(analysis, &owner, "shared_reference", &[root_id.serial()]);
        // This local view has zero charged bytes but still carries a strong
        // reference. Completing its source geometry must preserve that link.
        let mut local_view = owner.clone();
        local_view.view = crate::resource::memory::metadata::View::Local;
        local_view.source =
            Some((typ.clone(), SpannedTyped::new(&site, &typ, ExprX::Var(root.clone()))));
        assert_reference(analysis, &local_view, "shared_reference", &[root_id.serial()]);
        let records = analysis.owner_metadata(&site, &owner, &mut vec![]);
        // A forest consumer without the population interface must reject, even
        // though the linked owner itself has no charged bytes.
        assert!(
            analysis.owner_from_metadata(&site, &typ, records, Default::default(), false).is_err()
        );
        analysis.var_modes.insert(root.clone(), Mode::Exec);
        analysis.slots.insert(root.clone(), value);
        analysis.heap.owners.insert(root.clone(), owner);
        assert_eq!(analysis.storage.live(), 96); // handle + control + Box handle + payload
        let reference = Arc::new(TypX::Decorate(TypDecoration::Ref, None, typ.clone()));
        let argument = SpannedTyped::new(
            &site,
            &reference,
            ExprX::ReadPlace(
                SpannedTyped::new(&site, &typ, PlaceX::Local(root.clone())),
                UnfinalizedReadKind { preliminary_kind: ReadKind::ImmutBor, id: 0 },
            ),
        );
        let value = analysis
            .produce(&call(
                &span(2),
                &typ,
                ResourceIntrinsic::Concurrency(Operation::ArcClone),
                vec![argument],
            ))
            .unwrap();
        let owner = analysis.result_owner.take().unwrap();
        assert_eq!(owner.shared, identity);
        assert_reference(analysis, &owner, "shared_reference", &[root_id.serial()]);
        analysis.var_modes.insert(copy.clone(), Mode::Exec);
        analysis.slots.insert(copy.clone(), value);
        analysis.heap.owners.insert(copy.clone(), owner);
        let (id, handle_value) = spawn(analysis, handle, expression, 10);
        assert_eq!(analysis.storage.live(), 113); // two strong handles, one payload, worker + tag
        let owner = analysis.heap.owners.remove(&root).unwrap();
        analysis.release_owner(owner, &span(11));
        let value = analysis.slots.remove(&root).unwrap();
        analysis.release_value(value, &span(11));
        assert_eq!(analysis.storage.live(), 105);
        let mut entry = analysis.heap.workers.enter(id, &span(12)).unwrap();
        assert!(!entry.shared.is_empty());
        // An alternative body-analysis snapshot can release its imported
        // handle without changing this entry or freeing caller-owned backing.
        let mut alternative = entry.shared.clone();
        assert!(alternative.release(root_id).is_none());
        assert!(alternative.is_empty());
        assert!(!entry.shared.is_empty());
        assert_eq!(analysis.storage.live(), 105);
        let returned = entry.take_capture_owner(&(copy, vec![])).unwrap();
        let mut frame = entry.into_return_cleanup(analysis.layouts).unwrap();
        let environment = frame.owner.take().unwrap();
        assert_eq!(returned.shared, identity);
        analysis.release_owner(environment, &span(12));
        analysis
            .heap
            .workers
            .transition_completion(
                id,
                &span(13),
                Storage { typ, value: frame.value, owner: Some(returned) },
            )
            .unwrap();
        assert_eq!(analysis.storage.live(), 105);
        let result = finish_join(analysis, id, handle_value);
        assert_eq!(analysis.storage.live(), 96);
        assert_eq!(result.owner.as_ref().unwrap().shared, identity);
        analysis.release_owner(result.owner.unwrap(), &span(14));
        analysis.release_value(result.value, &span(14));
        assert!(analysis.heap.shared.is_empty());
        analysis.heap.workers.check_closed(&span(14)).unwrap();
        assert_eq!(analysis.storage.live(), 0);
        assert_eq!(analysis.storage.peak().bytes, 113);
    });
}

#[test]
fn detaching_and_waiting_do_not_release_running_storage() {
    let site = span(1);
    let initializer = source_box(&site);
    let source = VarIdent(Arc::new("source".into()), VarIdentDisambiguate::RustcId(1));
    let (info, expression) = closure(1, Some((source.clone(), initializer.typ.clone())));
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let value = analysis.produce(&initializer).unwrap();
        analysis.slots.insert(source.clone(), value);
        analysis.var_modes.insert(source.clone(), Mode::Exec);
        analysis.heap.owners.insert(source.clone(), analysis.result_owner.take().unwrap());
        let (id, handle_value) = spawn(analysis, handle, expression, 10);
        analysis.heap.workers.wait(id, None, &site, handle_value).unwrap();
        assert!(analysis.heap.workers.take_result(id, None, &site).is_err());
        assert_eq!(analysis.storage.live(), 81);
        let snapshot = analysis.heap.workers.clone();
        analysis.release_owner(
            Owner {
                worker: Some(super::FixedHandle { actor: id, publication: None }),
                ..Default::default()
            },
            &span(12),
        );
        assert_eq!(analysis.storage.live(), 81);
        assert!(!analysis.heap.workers.compatible(&snapshot));
        assert!(analysis.heap.workers.check_closed(&site).is_err());
    });
}

#[test]
fn parent_completion_requires_its_actual_child_to_be_joined() {
    let (parent, parent_expression) = closure(1, None);
    let (child, child_expression) = closure(2, None);
    let mut evidence = Evidence::default();
    evidence.closures.insert(parent.id, parent);
    evidence.closures.insert(child.id, child);
    with_analysis(&evidence, |analysis, handle| {
        analysis.heap.workers.check_closed(&span(0)).unwrap();
        let (parent, parent_handle) = spawn(analysis, handle, parent_expression, 10);
        let frame = analysis.heap.workers.enter(parent, &span(11)).unwrap().storage;
        if let Some(owner) = frame.owner {
            analysis.release_owner(owner, &span(11));
        }
        analysis.release_value(frame.value, &span(11));
        analysis.current_worker = Some(parent);
        let (child, child_handle) = spawn(analysis, handle, child_expression, 12);
        let frame = analysis.heap.workers.enter(child, &span(13)).unwrap().storage;
        if let Some(owner) = frame.owner {
            analysis.release_owner(owner, &span(13));
        }
        analysis.release_value(frame.value, &span(13));
        let output =
            || Storage { typ: crate::ast_util::unit_typ(), value: Value::unit(), owner: None };
        assert!(analysis.heap.workers.transition_completion(parent, &span(14), output()).is_err());
        analysis.heap.workers.transition_completion(child, &span(14), output()).unwrap();
        assert!(analysis.heap.workers.transition_completion(parent, &span(14), output()).is_err());
        finish_join(analysis, child, child_handle);
        analysis.heap.workers.transition_completion(parent, &span(15), output()).unwrap();
        analysis.current_worker = None;
        finish_join(analysis, parent, parent_handle);
        analysis.heap.workers.check_closed(&span(16)).unwrap();
        assert_eq!(analysis.storage.live(), 0);
    });
}

#[test]
fn join_waits_reject_cycles_and_resume_only_the_actual_waiting_actor() {
    let (info, expression) = closure(1, None);
    let mut evidence = Evidence::default();
    evidence.closures.insert(info.id, info);
    with_analysis(&evidence, |analysis, handle| {
        let (first, first_handle) = spawn(analysis, handle, expression.clone(), 10);
        let (second, second_handle) = spawn(analysis, handle, expression.clone(), 11);
        let (third, third_handle) = spawn(analysis, handle, expression, 12);
        for id in [first, second, third] {
            let frame = analysis.heap.workers.enter(id, &span(13)).unwrap().storage;
            if let Some(owner) = frame.owner {
                analysis.release_owner(owner, &span(13));
            }
            analysis.release_value(frame.value, &span(13));
        }
        let workers = &mut analysis.heap.workers;
        // Cloned metadata describes rejected candidate edges, not executable
        // copies of a Rust join handle. Failed validation changes no ownership.
        assert!(workers.wait(first, Some(first), &span(14), first_handle.clone()).is_err());
        workers.wait(second, Some(first), &span(15), second_handle).unwrap();
        assert!(workers.wait(first, Some(second), &span(16), first_handle.clone()).is_err());
        workers.wait(third, Some(second), &span(17), third_handle).unwrap();
        assert!(workers.wait(first, Some(third), &span(18), first_handle.clone()).is_err());
        workers.wait(first, None, &span(19), first_handle).unwrap();
        assert!(workers.blocked(None));
        assert!(workers.blocked(Some(first)));
        assert!(workers.blocked(Some(second)));
        assert!(!workers.blocked(Some(third)));
        assert!(workers.transition_completion(first, &span(20), empty_result()).is_err());
        assert!(workers.transition_completion(second, &span(20), empty_result()).is_err());
        // Even the actual waiter cannot collect the result or shed its handle
        // charge while its child is still running.
        assert!(workers.take_result(third, Some(second), &span(20)).is_err());
        assert!(workers.blocked(Some(second)));
        assert_eq!(analysis.storage.live(), 27);
        workers.transition_completion(third, &span(21), empty_result()).unwrap();
        assert!(workers.take_result(third, Some(first), &span(22)).is_err());
        assert_eq!(analysis.storage.live(), 27);
        analysis.current_worker = Some(second);
        analysis.collect_worker_result(third, &span(23)).unwrap();
        assert_eq!(analysis.storage.live(), 18);
        assert!(!analysis.heap.workers.blocked(Some(second)));
        assert!(analysis.heap.workers.blocked(Some(first)));
        analysis.heap.workers.transition_completion(second, &span(24), empty_result()).unwrap();
        analysis.current_worker = Some(first);
        analysis.collect_worker_result(second, &span(25)).unwrap();
        assert_eq!(analysis.storage.live(), 9);
        assert!(!analysis.heap.workers.blocked(Some(first)));
        assert!(analysis.heap.workers.blocked(None));
        analysis.heap.workers.transition_completion(first, &span(26), empty_result()).unwrap();
        analysis.current_worker = None;
        analysis.collect_worker_result(first, &span(27)).unwrap();
        assert_eq!(analysis.storage.live(), 0);
        assert!(!analysis.heap.workers.blocked(None));
        analysis.heap.workers.check_closed(&span(28)).unwrap();
    });
}

#[test]
fn completion_moves_only_the_inline_payload_to_the_heap_record() {
    use crate::resource::memory::{
        contracts,
        footprint::{Footprint, MemoryKind, MemorySelection},
    };
    let site = span(1);
    let local = MemoryKind::host_local();
    let heap = MemoryKind::host_heap();
    // The blocked caller has an 8-byte handle. A 24-byte Vec is returned
    // with a 64-byte buffer. The existing completion tag costs one byte.
    let live = Footprint::charge(local.clone(), contracts::literal(&site, 32))
        .add(&site, Footprint::charge(heap.clone(), contracts::literal(&site, 65)));
    let ready = states::completed(&site, live, 24);
    for (selection, bytes) in [
        (MemorySelection::kind(local), 8),
        (MemorySelection::kind(heap), 89),
        (MemorySelection::All, 97),
    ] {
        assert_eq!(contracts::constant(&ready.select(&site, &selection)), Some(bytes));
    }
}
