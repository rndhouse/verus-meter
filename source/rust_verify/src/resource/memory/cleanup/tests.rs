//! These fixtures compile ordinary executable Rust. Assertions inspect the
//! emitted compiler graph, never a manually supplied allocation/sync model.
use super::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use std::sync::Arc;
use vir::resource::memory::synchronization::Operation;

#[test]
fn compiler_identifies_native_publication_join_and_shared_aliases() {
    use vir::resource::memory::concurrency::Operation as C;
    let graphs = compile(
        r#"
        use std::sync::Arc as Shared;
        pub fn native() {
            let first = Shared::new(7u64);
            let alias = Shared::clone(&first);
            let _view = <Shared<u64> as std::ops::Deref>::deref(&first);
            let handle = std::thread::spawn(move || alias);
            let result = handle.join();
            drop(result);
        }
        mod fake {
            pub struct Arc;
            impl Arc {
                pub fn new() -> Self { Self }
                pub fn clone(&self) -> Self { Self }
            }
            pub struct JoinHandle;
            impl JoinHandle { pub fn join(self) {} }
            pub fn spawn(_: Arc) -> JoinHandle { JoinHandle }
        }
        pub fn unrelated() {
            let original = fake::Arc::new();
            fake::spawn(original.clone()).join();
        }
    "#,
    );
    let native = &graphs["native"];
    let operations: Vec<_> = native
        .blocks
        .iter()
        .filter_map(|block| match block.terminator {
            Terminator::Call { call: Call::Concurrent(operation), .. } => Some(operation),
            _ => None,
        })
        .collect();
    assert_eq!(operations, [C::ArcNew, C::ArcClone, C::ArcBorrow, C::StdSpawn, C::StdJoin]);
    assert!(!graphs["unrelated"].blocks.iter().any(|block| matches!(
        block.terminator,
        Terminator::Call { call: Call::Concurrent(_), .. }
    )));
}

fn compile(source: &str) -> HashMap<String, Graph> {
    struct Test {
        source: String,
        graphs: HashMap<String, Graph>,
    }
    impl Callbacks for Test {
        fn config(&mut self, config: &mut rustc_interface::interface::Config) {
            config.file_loader =
                Some(Box::new(crate::trait_check::TCFileLoader { rust_code: self.source.clone() }));
        }

        fn after_analysis<'tcx>(&mut self, _: &Compiler, tcx: ty::TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Fn) {
                    continue;
                }
                let graph = lower(
                    tcx,
                    owner,
                    &|id| {
                        Arc::new(vir::ast::FunX {
                            path: Arc::new(vir::ast::PathX {
                                krate: vir::ast::CrateId::Internal,
                                segments: Arc::new(vec![vir::ast::Segment::V(
                                    Arc::new(tcx.def_path_str(id)),
                                    0,
                                )]),
                            }),
                        })
                    },
                    &|span| Span {
                        raw_span: Arc::new(span.data()),
                        id: 0,
                        data: Arc::new([]),
                        as_string: format!("{span:?}").into(),
                    },
                );
                self.graphs.insert(tcx.item_name(owner.to_def_id()).to_string(), graph);
            }
            Compilation::Stop
        }
    }
    let mut test = Test { source: source.into(), graphs: HashMap::new() };
    let sysroot = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .expect("prepared rustc");
    assert!(sysroot.status.success());
    rustc_driver::run_compiler(
        &[
            "rustc".into(),
            "--crate-name=sync_cleanup_test".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "--sysroot".into(),
            String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            "dummyrs.rs".into(),
        ],
        &mut test,
    );
    test.graphs
}

fn binding(graph: &Graph, name: &str) -> Place {
    let matches: Vec<_> = graph.bindings.iter().filter(|(var, _)| var.0.as_str() == name).collect();
    assert_eq!(matches.len(), 1, "binding {name} in {graph:#?}");
    matches[0].1.place.clone()
}

#[test]
fn compiler_preserves_moves_and_explicit_drop() {
    let graphs = compile(
        r#"
        use std::sync::Mutex;
        #[allow(dropping_references)]
        pub fn moved(mutex: &Mutex<u64>) {
            let alias = mutex;
            let original = alias.lock();
            let moved = original;
            let borrowed = &moved;
            drop(borrowed);
            drop(moved);
        }
    "#,
    );
    let graph = &graphs["moved"];
    let original = binding(graph, "original");
    let moved = binding(graph, "moved");
    let borrowed = binding(graph, "borrowed");
    let statements: Vec<_> = graph.blocks.iter().flat_map(|block| &block.statements).collect();
    assert!(statements.iter().any(|(_, stmt)| matches!(stmt,
        Statement::Assign(to, Value::Use(Operand::Move(from)))
        if *to == moved && *from == original)));
    assert!(statements.iter().any(|(_, stmt)| matches!(stmt,
        Statement::Assign(to, Value::Borrow(from)) if *to == borrowed && *from == moved)));
    let drop_calls: Vec<_> = graph
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::Call { call: Call::Drop, .. }))
        .collect();
    assert_eq!(drop_calls.len(), 2);
    assert!(statements.iter().any(|(_, stmt)| matches!(stmt,
        Statement::Assign(to, Value::Use(Operand::Copy(from)))
        if *from == borrowed && drop_calls.iter().any(|block| matches!(&block.terminator,
            Terminator::Call { arguments, .. } if arguments == &[Operand::Move(to.clone())])))));
    // Drop receives a moved temporary; it does not receive a fresh acquisition.
    assert!(statements.iter().any(|(_, stmt)| matches!(stmt,
        Statement::Assign(to, Value::Use(Operand::Move(from)))
        if *from == moved && drop_calls.iter().any(|block| matches!(&block.terminator,
            Terminator::Call { arguments, .. } if arguments == &[Operand::Move(to.clone())])))));
    assert_eq!(
        graph
            .blocks
            .iter()
            .filter(|block| matches!(
                block.terminator,
                Terminator::Call { call: Call::Primitive(Operation::MutexLock), .. }
            ))
            .count(),
        1
    );
    let outcomes = graph
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Terminator::Call { call: Call::Primitive(Operation::MutexLock), outcomes, .. } => {
                Some(outcomes)
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(
        outcomes.iter().map(|o| o.outcome).collect::<Vec<_>>(),
        [Outcome::Acquired, Outcome::Poisoned]
    );
    assert!(outcomes.iter().all(|o| o.guard.is_some()));
}

#[test]
fn compiler_retains_returned_guards_and_helper_boundaries() {
    let graphs = compile(
        r#"
        use std::sync::{Mutex, MutexGuard, LockResult};
        pub fn helper(m: &Mutex<u64>) -> LockResult<MutexGuard<'_, u64>> { m.lock() }
        pub fn caller(m: &Mutex<u64>) {
            let result = helper(m);
            let wrapped = (result,);
            drop(wrapped);
        }
    "#,
    );
    let helper = &graphs["helper"];
    assert!(helper.blocks.iter().any(|block| matches!(&block.terminator,
        Terminator::Call { call: Call::Primitive(Operation::MutexLock), destination, .. }
        if destination.local == 0 && destination.projection.is_empty())));
    let caller = &graphs["caller"];
    let result = binding(caller, "result");
    let wrapped = binding(caller, "wrapped");
    assert!(caller.blocks.iter().any(|block| matches!(&block.terminator,
        Terminator::Call { call: Call::Function(fun), destination, outcomes, .. }
        if vir::ast_util::path_as_friendly_rust_name(&fun.path).ends_with("helper")
            && *destination == result && outcomes.is_empty())));
    let statements: Vec<_> = caller.blocks.iter().flat_map(|b| &b.statements).collect();
    let temporary = statements
        .iter()
        .find_map(|(_, stmt)| match stmt {
            Statement::Assign(target, Value::Aggregate { fields, .. }) if *target == wrapped => {
                match fields.as_slice() {
                    [Operand::Move(place)] => Some(place),
                    _ => None,
                }
            }
            _ => None,
        })
        .expect("owning tuple field");
    assert!(statements.iter().any(|(_, stmt)| matches!(stmt,
        Statement::Assign(target, Value::Use(Operand::Move(source)))
        if target == temporary && *source == result)));
}

#[test]
fn compiler_preserves_implicit_drop_order_after_last_use() {
    let graphs = compile(
        r#"
        use std::sync::Mutex;
        pub fn implicit(a: &Mutex<u64>, b: &Mutex<u64>) {
            let first = a.lock();
            let second = b.lock();
            std::hint::black_box(&first);
            std::hint::black_box(&second);
        }
    "#,
    );
    let graph = &graphs["implicit"];
    let first = binding(graph, "first");
    let second = binding(graph, "second");
    // Follow normal compiler edges. These calls have no result discrimination,
    // so this path includes both acquired/poisoned Result destructor cases.
    let mut current = 0;
    let mut drops = Vec::new();
    loop {
        assert!(!graph.blocks[current].cleanup);
        match &graph.blocks[current].terminator {
            Terminator::Call { next: Some(next), .. } | Terminator::Goto(next) => current = *next,
            Terminator::Drop { place, next, .. } => {
                drops.push(place.clone());
                current = *next;
            }
            Terminator::Return => break,
            other => panic!("unexpected normal effect {other:?}"),
        }
    }
    assert_eq!(drops, [second, first]);
    assert!(graph.blocks.iter().any(|block| block.cleanup));
}

#[test]
fn compiler_cleans_up_on_early_return() {
    let graphs = compile(
        r#"
        use std::sync::Mutex;
        pub fn early(m: &Mutex<u64>, leave: bool) {
            let held = m.lock();
            if leave { return; }
            std::hint::black_box(&held);
        }
    "#,
    );
    let graph = &graphs["early"];
    let held = binding(graph, "held");
    let mut pending = vec![(0, Vec::new())];
    let mut returns = Vec::new();
    while let Some((index, mut drops)) = pending.pop() {
        assert!(!graph.blocks[index].cleanup);
        match &graph.blocks[index].terminator {
            Terminator::Goto(next) | Terminator::Call { next: Some(next), .. } => {
                pending.push((*next, drops));
            }
            Terminator::Switch { targets, otherwise, .. } => {
                for next in targets.iter().map(|(_, next)| *next).chain([*otherwise]) {
                    pending.push((next, drops.clone()));
                }
            }
            Terminator::Drop { place, next, .. } => {
                drops.push(place.clone());
                pending.push((*next, drops));
            }
            Terminator::Return => returns.push(drops),
            Terminator::Unreachable => {}
            other => panic!("unexpected normal effect {other:?}"),
        }
    }
    assert_eq!(returns.len(), 2);
    assert!(returns.iter().all(|drops| drops == std::slice::from_ref(&held)));
}

#[test]
fn compiler_distinguishes_shadowed_instances_and_reacquisitions() {
    let graphs = compile(
        r#"
        use std::sync::Mutex;
        #[allow(dropping_references)]
        pub fn identities() {
            let m = Mutex::new(0u64);
            let mut guard = m.lock();
            drop(&mut guard);
            drop(guard);
            let guard = m.lock();
            drop(guard);
            let m = Mutex::new(0u64);
            let guard = m.lock();
            drop(guard);
        }
    "#,
    );
    let graph = &graphs["identities"];
    for (name, expected) in [("m", 2), ("guard", 3)] {
        let locals: std::collections::HashSet<_> = graph
            .bindings
            .iter()
            .filter(|(variable, _)| variable.0.as_str() == name)
            .map(|(_, binding)| binding.place.local)
            .collect();
        assert_eq!(locals.len(), expected, "distinct binding places for {name}");
    }
    let sites: Vec<_> = graph
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(block, body)| match &body.terminator {
            Terminator::Call {
                call: Call::Primitive(Operation::MutexLock), destination, ..
            } => Some((Point { block, statement: body.statements.len() }, destination.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(sites.len(), 3);
    assert!(sites.windows(2).all(|pair| pair[0].0 != pair[1].0 && pair[0].1 != pair[1].1));
}

#[test]
fn compiler_retains_result_branches_and_unmodeled_calls() {
    let graphs = compile(
        r#"
        use std::sync::{Mutex, TryLockError};
        pub fn outcomes(m: &Mutex<u64>) {
            match m.try_lock() {
                Ok(guard) => drop(guard),
                Err(TryLockError::Poisoned(poison)) => drop(poison),
                Err(TryLockError::WouldBlock) => (),
            }
        }
        pub fn leaked(m: &Mutex<u64>) {
            let guard = m.lock();
            std::mem::forget(guard);
        }
    "#,
    );
    let graph = &graphs["outcomes"];
    assert!(graph.blocks.iter().any(|block| matches!(
        block.terminator,
        Terminator::Call { call: Call::Primitive(Operation::MutexTryLock), .. }
    )));
    let outcomes = graph
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Terminator::Call {
                call: Call::Primitive(Operation::MutexTryLock), outcomes, ..
            } => Some(outcomes),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        outcomes.iter().map(|o| o.outcome).collect::<Vec<_>>(),
        [Outcome::Acquired, Outcome::Poisoned, Outcome::WouldBlock]
    );
    assert!(outcomes[0].guard.is_some() && outcomes[1].guard.is_some());
    assert!(outcomes[2].guard.is_none());
    assert_eq!(outcomes[2].conditions.len(), 2);
    // Ignore additional compiler drop-flag switches. What matters is that both
    // actual result/error tags remain executable branch operands.
    for condition in &outcomes[2].conditions {
        let tag = graph
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|(_, stmt)| match stmt {
                Statement::Assign(target, Value::Discriminant(source))
                    if source == &condition.place =>
                {
                    Some(target)
                }
                _ => None,
            })
            .expect("executable result discriminant");
        assert!(graph.blocks.iter().any(|block| matches!(&block.terminator,
            Terminator::Switch { operand: Operand::Move(source) | Operand::Copy(source), .. }
            if source == tag)));
    }
    assert!(graph.blocks.iter().flat_map(|block| &block.statements).any(
        |(_, stmt)| matches!(stmt,
        Statement::Assign(_, Value::Use(Operand::Move(Place { projection, .. })))
        if projection.contains(&Projection::Variant(1)))
    ));
    let leaked = &graphs["leaked"];
    assert!(leaked.blocks.iter().any(|block| matches!(&block.terminator,
        Terminator::Call { call: Call::Function(fun), .. }
        if vir::ast_util::path_as_friendly_rust_name(&fun.path).ends_with("::forget"))));
    assert!(!leaked.blocks.iter().any(|block| matches!(
        &block.terminator,
        Terminator::Call { call: Call::Drop, .. } | Terminator::Drop { .. }
    )));
}
