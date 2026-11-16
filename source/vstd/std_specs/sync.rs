//! Opaque Rust synchronization types. Their memory layouts and exclusion effects
//! are supplied by compiler-identified resource contracts, not by field access or
//! ordinary functional axioms here. Runtime memory proofs still require the
//! synchronization lifetime analysis; a type declaration alone cannot grant one.
use super::super::prelude::*;
use std::sync::{Mutex, MutexGuard, PoisonError, TryLockError};

verus! {

/// Opaque specification of a standard mutex, without exposing its runtime fields.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExMutex<T: ?Sized>(Mutex<T>);

/// Opaque guard type; Rust retains its ownership, lifetime and thread restrictions.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExMutexGuard<'a, T: ?Sized + 'a>(MutexGuard<'a, T>);

/// A poison outcome can retain an acquired guard as its opaque payload.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExPoisonError<T>(PoisonError<T>);

/// Expose the native variants so executable code can distinguish WouldBlock from
/// an acquiring poison error. The PoisonError payload itself remains opaque.
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
pub struct ExTryLockError<T>(TryLockError<T>);

// These deliberately weak functional specifications expose the native surface
// without assuming success, progress, an unpoisoned state or a payload invariant.
// Reviewed compiler resource contracts carry exclusion and conditional ownership;
// ordinary user postconditions cannot create those effects.
pub assume_specification<T>[ Mutex::<T>::new ](value: T) -> (mutex: Mutex<T>)
;

pub assume_specification<'a, T: ?Sized>[ Mutex::<T>::lock ](mutex: &'a Mutex<T>) -> (result: Result<
    MutexGuard<'a, T>,
    PoisonError<MutexGuard<'a, T>>,
>)
;

pub assume_specification<'a, T: ?Sized>[ Mutex::<T>::try_lock ](mutex: &'a Mutex<T>) -> (result:
    Result<MutexGuard<'a, T>, TryLockError<MutexGuard<'a, T>>>)
;

pub assume_specification<'a, 'b, T: ?Sized>[ <MutexGuard<'a, T> as core::ops::Deref>::deref ](
    guard: &'b MutexGuard<'a, T>,
) -> (value: &'b T)
;

pub assume_specification<'a, 'b, T: ?Sized>[ <MutexGuard<
    'a,
    T,
> as core::ops::DerefMut>::deref_mut ](guard: &'b mut MutexGuard<'a, T>) -> (value: &'b mut T)
;

} // verus!
