//! Functional specifications for native Rust thread handles. Success is not
//! assumed: the resource analysis separately checks the closed, panic-free worker
//! domain and the environmental thread-creation assumption.
use super::super::prelude::*;

verus! {

/// A native handle retains its worker's completion record until joining.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExJoinHandle<T>(std::thread::JoinHandle<T>);

/// Ordinary functional information passed from a closure to a successful join.
pub trait JoinHandleSpec<T> {
    spec fn result_predicate(&self, value: T) -> bool;
}

impl<T> JoinHandleSpec<T> for std::thread::JoinHandle<T> {
    uninterp spec fn result_predicate(&self, value: T) -> bool;
}

pub assume_specification<F, T>[ std::thread::spawn ](worker: F) -> (handle: std::thread::JoinHandle<
    T,
>) where F: FnOnce() -> T + Send + 'static, T: Send + 'static
    requires
        worker.requires(()),
    ensures
        forall|value: T| #[trigger] handle.result_predicate(value) ==> worker.ensures((), value),
;

pub assume_specification<T>[ std::thread::JoinHandle::<T>::join ](
    handle: std::thread::JoinHandle<T>,
) -> (result: std::thread::Result<T>)
    ensures
        match result {
            Ok(value) => handle.result_predicate(value),
            Err(_) => true,
        },
;

} // verus!
