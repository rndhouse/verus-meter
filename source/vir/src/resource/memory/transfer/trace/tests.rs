//! Regression checks at the boundary between checked operations and templates.

use super::*;
use crate::resource::memory::layout::Layouts;

fn span(id: u64) -> Span {
    Span { raw_span: Arc::new(()), id, data: Arc::new([]), as_string: "checked transfer".into() }
}

fn with_trace(checked: &Checked, test: impl FnOnce(&mut Trace<'_>)) {
    let layouts = Layouts::new(&[], None, None, None);
    let functions = HashMap::new();
    let summaries = HashMap::new();
    let modes = HashMap::new();
    test(&mut Trace {
        layouts: &layouts,
        functions: &functions,
        summaries: &summaries,
        modes: &modes,
        checked,
        used: HashSet::new(),
        state: State::default(),
        symbols: vec![],
        regions: BTreeMap::new(),
        effects: vec![],
        branch_depth: 0,
        loop_tokens: None,
        loop_roots: None,
        loop_inputs: HashMap::new(),
        loop_allocations: Vec::new(),
        loop_calls: Vec::new(),
        loop_scratch: HashMap::new(),
        loop_repetitions: HashMap::new(),
        loop_size_ceiling: 0,
        allocation_checks: Vec::new(),
        loop_transfers: HashMap::new(),
        loop_growth: HashMap::new(),
        proof_values: HashMap::new(),
    });
}

#[test]
fn constructor_requires_a_checked_rule_and_does_not_reenter_on_its_constant() {
    let span = span(1);
    let payload_type = Arc::new(TypX::Int(IntRange::U(128)));
    let typ = Arc::new(TypX::Decorate(TypDecoration::Box, None, payload_type.clone()));
    let payload = SpannedTyped::new(&span, &payload_type, expr::integer(&span, 0).x.clone());
    // Checked allocation operands can share the constructor's span, as with
    // the zero capacity synthesized for Vec::new(). They are scalar values.
    let source = expr::operation(&span, "constructor", vec![payload.clone()], typ);
    with_trace(&Checked::default(), |trace| assert!(trace.value(&source).is_none()));
    let mut checked = Checked::default();
    checked.operation(&span, checked::Operation::Box { payload, bytes: 16 });
    with_trace(&checked, |trace| {
        let Some(Value::Owner(node)) = trace.value(&source) else { panic!("missing constructor") };
        assert_eq!(contracts::constant(&property(&span, node.memory, "bytes")), Some(16));
        assert!(checked.covered(&trace.used));
    });
}

#[test]
fn movement_uses_the_checked_dereference_and_cannot_be_invented_or_skipped() {
    let span = span(2);
    let child_type =
        Arc::new(TypX::Decorate(TypDecoration::Box, None, Arc::new(TypX::Int(IntRange::U(8)))));
    let outer_type = Arc::new(TypX::Decorate(TypDecoration::Box, None, child_type.clone()));
    let name = VarIdent(Arc::new("owner".into()), VarIdentDisambiguate::VirTemp(1));
    // Lowering retains the outer place type while accounting selects its
    // contents. Re-resolving from place.typ would consume the wrong tree.
    let place = SpannedTyped::new(&span, &outer_type, PlaceX::Local(name.clone()));
    let source = SpannedTyped::new(
        &span,
        &child_type,
        ExprX::ReadPlace(
            place.clone(),
            UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
        ),
    );
    let descriptor = |bytes| {
        expr::push(
            &span,
            expr::empty(&span, expr::record_type()),
            allocated(
                &span,
                expr::integer(&span, bytes),
                expr::integer(&span, 0),
                expr::integer(&span, 0),
            ),
        )
    };
    let parent = Node {
        origin: None,
        typ: outer_type,
        memory: expr::add(
            &span,
            descriptor(8),
            expr::prefix(&span, descriptor(1), expr::path(&span, [-1])),
        ),
        minima: Minima::new(),
    };
    with_trace(&Checked::default(), |trace| {
        trace.state.values.insert(name.clone(), Value::Owner(parent.clone()));
        assert!(trace.place_value(&place, &place.typ).is_none());
        assert!(trace.state.values.contains_key(&name));
    });
    let mut checked = Checked::default();
    checked.movement(
        &span,
        checked::Place {
            source,
            typ: child_type.clone(),
            location: (name.clone(), vec![OwnerSlot::Contents]),
        },
    );
    with_trace(&checked, |trace| {
        trace.state.values.insert(name.clone(), Value::Owner(parent));
        assert!(!checked.covered(&trace.used));
        let Some(Value::Owner(child)) = trace.place_value(&place, &place.typ) else {
            panic!("missing move")
        };
        assert!(crate::ast_util::types_equal(&child.typ, &child_type));
        assert_eq!(contracts::constant(&property(&span, child.memory, "bytes")), Some(1));
        let Value::Owner(parent) = &trace.state.values[&name] else { panic!("parent consumed") };
        assert_eq!(contracts::constant(&property(&span, parent.memory.clone(), "bytes")), Some(8));
        assert!(checked.covered(&trace.used));
    });
}

#[test]
fn even_read_only_loops_require_body_accounting_and_consume_its_record() {
    let span = span(3);
    let source = SpannedTyped::new(
        &span,
        &crate::ast_util::unit_typ(),
        ExprX::Loop {
            loop_isolation: true,
            allow_complex_invariants: false,
            is_for_loop: false,
            assume_termination: false,
            label: Label { id: 0, name: None },
            cond: Some(crate::ast_util::mk_bool(&span, false)),
            body: crate::ast_util::mk_block(&span, vec![], None),
            invs: Arc::new(vec![]),
            decrease: Arc::new(vec![]),
            atomic_call: false,
            known_no_back_edge: false,
            source: LoopSource::Loop,
        },
    );
    with_trace(&Checked::default(), |trace| assert!(trace.value(&source).is_none()));
    let mut checked = Checked::default();
    let record = crate::resource::memory::loops::Loop::new(
        &source,
        &Layouts::new(&[], None, None, None),
        &HashMap::new(),
    )
    .unwrap();
    checked.loops.insert(span.id, record);
    with_trace(&checked, |trace| {
        assert!(!checked.covered(&trace.used));
        assert!(matches!(trace.value(&source), Some(Value::Unit)));
        assert!(checked.covered(&trace.used));
    });
}

/// Selecting one fixed role must discard branch-dependent siblings before the
/// next update, rather than embedding the complete joined owner in that role.
#[test]
fn conditional_projection_keeps_only_the_selected_role() {
    let span = span(10);
    let name = |value: &str| VarIdent(Arc::new(value.into()), VarIdentDisambiguate::VirTemp(10));
    let source = SpannedTyped::new(&span, &expr::memory_type(), ExprX::Var(name("source")));
    let other = SpannedTyped::new(&span, &expr::memory_type(), ExprX::Var(name("other")));
    let condition = SpannedTyped::new(&span, &bool_typ(), ExprX::Var(name("choose")));
    let source_path = expr::path(&span, [-1]);
    let yes = expr::add(
        &span,
        expr::prefix(&span, source.clone(), source_path.clone()),
        expr::prefix(&span, other, expr::path(&span, [-2])),
    );
    let no = expr::prefix(&span, source.clone(), source_path.clone());
    let joined = choice(&span, condition, yes, no);
    let selected = simplify::simplify(&expr::subtree(&span, joined, source_path));
    assert!(simplify::same_expression(&selected, &source), "{selected:?}");
}
