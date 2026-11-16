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

/// Opaque try-lock failure, distinguished by the resource contract on acquisition.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExTryLockError<T>(TryLockError<T>);

} // verus!
