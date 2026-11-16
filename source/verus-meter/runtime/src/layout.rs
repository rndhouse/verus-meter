//! Rust resolves these types, including aliases. Constants describe source model
//! storage, never ABI size or allocator overhead. Struct layouts require a later
//! compiler bridge and deliberately have no implementation here.
use verus_meter_model::{BOOL_BYTES, WORD_BYTES, array_bytes, integer_bytes, reference_bytes};

/// Inline storage for a type supported by runtime model-size queries.
#[doc(hidden)]
pub trait ValueSize {
    /// Source-model inline bytes, excluding separate allocations.
    const BYTES: u64;
}

/// Reference-handle storage for a supported reference type.
#[doc(hidden)]
pub trait ReferenceSize {
    /// Source-model bytes occupied by the reference handle.
    const BYTES: u64;
}

mod sealed {
    pub trait Integer {}
}

macro_rules! integers {
    ($($ty:ty => $bits:expr),* $(,)?) => {
        $(impl sealed::Integer for $ty {}
        impl ValueSize for $ty {
            const BYTES: u64 = integer_bytes($bits).unwrap();
        })*
    };
}

integers!(u8 => 8, i8 => 8, u16 => 16, i16 => 16, u32 => 32, i32 => 32, u64 => 64, i64 => 64, u128 => 128, i128 => 128);

impl sealed::Integer for usize {}

impl sealed::Integer for isize {}

impl ValueSize for usize {
    const BYTES: u64 = WORD_BYTES;
}

impl ValueSize for isize {
    const BYTES: u64 = WORD_BYTES;
}

impl ValueSize for bool {
    const BYTES: u64 = BOOL_BYTES;
}

impl ValueSize for () {
    const BYTES: u64 = 0;
}

impl<T: ValueSize + sealed::Integer, const N: usize> ValueSize for [T; N] {
    const BYTES: u64 = match array_bytes(T::BYTES, N as u64) {
        Some(bytes) => bytes,
        None => panic!("model array size exceeds u64"),
    };
}

impl<T> ValueSize for Vec<T> {
    const BYTES: u64 = 3 * WORD_BYTES;
}

impl<T: ValueSize> ValueSize for Option<T> {
    const BYTES: u64 = T::BYTES + BOOL_BYTES;
}

impl<T> ValueSize for Box<T> {
    const BYTES: u64 = WORD_BYTES;
}

impl<T> ValueSize for Box<[T]> {
    const BYTES: u64 = 2 * WORD_BYTES;
}

impl<T> ReferenceSize for &T {
    const BYTES: u64 = reference_bytes(false);
}

impl<T> ReferenceSize for &mut T {
    const BYTES: u64 = reference_bytes(false);
}

impl<T> ReferenceSize for &[T] {
    const BYTES: u64 = reference_bytes(true);
}

impl<T> ReferenceSize for &mut [T] {
    const BYTES: u64 = reference_bytes(true);
}
