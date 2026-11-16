use super::*;
use crate::ast::VarIdentDisambiguate;
use std::sync::Arc;

fn name(s: &str) -> VarIdent {
    VarIdent(Arc::new(s.into()), VarIdentDisambiguate::RustcId(0))
}

#[test]
fn aliases_moves_and_reacquisition_keep_distinct_intervals() {
    let mut state = Effects::default();
    let mutex = state.construct(name("mutex")).unwrap();
    state.borrow(&name("mutex"), name("alias")).unwrap();
    let first = state
        .acquire(&name("alias"), name("g"), Operation::MutexLock, Outcome::Acquired)
        .unwrap()
        .unwrap();
    state.move_to(&name("g"), name("moved")).unwrap();
    assert_eq!(state.instance(&name("g")), None);
    assert_eq!(state.instance(&name("moved")), Some(mutex));
    state.borrow(&name("moved"), name("view")).unwrap();
    state.release(&name("moved")).unwrap();
    assert_eq!(state.instance(&name("view")), None);
    let second = state
        .acquire(&name("mutex"), name("g"), Operation::MutexLock, Outcome::Acquired)
        .unwrap()
        .unwrap();
    assert_ne!(first, second);
    assert_eq!(state.events()[1], Event::Release { instance: mutex, acquisition: first });
}

#[test]
fn separate_instances_and_borrowed_views_do_not_create_exclusion() {
    let mut state = Effects::default();
    let a = state.construct(name("a")).unwrap();
    let b = state.construct(name("b")).unwrap();
    assert_ne!(a, b);
    state.acquire(&name("a"), name("g"), Operation::MutexLock, Outcome::Acquired).unwrap();
    state.borrow(&name("g"), name("view")).unwrap();
    assert_eq!(state.events().len(), 1);
    assert_eq!(state.release(&name("view")), Err(EffectError::BorrowedRelease));
    state.acquire(&name("b"), name("other"), Operation::MutexLock, Outcome::Acquired).unwrap();
    assert_eq!(state.events().len(), 2);
}

#[test]
fn outcomes_and_reentrancy_do_not_fabricate_guards() {
    let mut state = Effects::default();
    state.construct(name("m")).unwrap();
    assert_eq!(
        state.acquire(&name("m"), name("g"), Operation::MutexTryLock, Outcome::WouldBlock),
        Ok(None)
    );
    assert_eq!(state.instance(&name("g")), None);
    assert!(state.events().is_empty());
    state.acquire(&name("m"), name("poison"), Operation::MutexLock, Outcome::Poisoned).unwrap();
    assert!(matches!(state.events()[0], Event::Acquire { outcome: Outcome::Poisoned, .. }));
    assert_eq!(
        state.acquire(&name("m"), name("g"), Operation::MutexLock, Outcome::Acquired),
        Err(EffectError::ReentrantAcquire)
    );
    assert_eq!(
        state.acquire(&name("m"), name("g"), Operation::MutexTryLock, Outcome::Acquired),
        Err(EffectError::InvalidOutcome)
    );
    assert_eq!(state.events().len(), 1);
}
