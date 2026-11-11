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
        appends: false,
        effects: vec![],
        branch_depth: 0,
        loop_tokens: None,
        loop_invariants: HashMap::new(),
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
