//! Rust resolves these types, including aliases. Constants describe source model
//! storage, never ABI size or allocator overhead. Struct layouts require a later
//! compiler bridge and deliberately have no implementation here.
use verus_meter_model::{BOOL_BYTES, WORD_BYTES, array_bytes, integer_bytes, reference_bytes};

/// Inline storage for a type supported by runtime model-size queries.
///
/// Implementations are sealed: generated queries must use the runtime's model
/// policy, never a caller-supplied byte count for a custom type.
///
/// ```compile_fail,E0277
/// struct Buffer([u8; 64]);
/// impl verus_meter_runtime::ValueSize for Buffer {
///     const BYTES: u64 = 0;
/// }
/// ```
#[doc(hidden)]
pub trait ValueSize: sealed::Value {
    /// Source-model inline bytes, excluding separate allocations.
    const BYTES: u64;
}

/// Reference-handle storage for a supported reference type.
///
/// Like inline sizes, reference sizes follow a sealed model policy.
///
/// ```compile_fail,E0277
/// struct Buffer([u8; 64]);
/// impl verus_meter_runtime::ReferenceSize for Buffer {
///     const BYTES: u64 = 0;
/// }
/// ```
#[doc(hidden)]
pub trait ReferenceSize: sealed::Reference {
    /// Source-model bytes occupied by the reference handle.
    const BYTES: u64;
}

/// Inline body state for a forward loop over a supported shared collection.
#[doc(hidden)]
pub trait ForLoopSize: sealed::ForLoop {
    /// Source-model bytes live alongside the user body.
    const BYTES: u64;
}

impl<T> sealed::ForLoop for &[T] {}

impl<T> ForLoopSize for &[T] {
    const BYTES: u64 = verus_meter_model::borrowed_for_loop_bytes(true);
}

impl<T> sealed::ForLoop for &Vec<T> {}

impl<T> ForLoopSize for &Vec<T> {
    const BYTES: u64 = verus_meter_model::borrowed_for_loop_bytes(false);
}

mod sealed {
    pub trait ForLoop {}

    pub trait Value {}

    pub trait Reference {}

    pub trait Integer {}
}

macro_rules! integers {
    ($($ty:ty => $bits:expr),* $(,)?) => {
        $(impl sealed::Integer for $ty {}
        impl sealed::Value for $ty {}
        impl ValueSize for $ty {
            const BYTES: u64 = integer_bytes($bits).unwrap();
        })*
    };
}

integers!(u8 => 8, i8 => 8, u16 => 16, i16 => 16, u32 => 32, i32 => 32, u64 => 64, i64 => 64, u128 => 128, i128 => 128);

impl sealed::Integer for usize {}

impl sealed::Integer for isize {}

impl sealed::Value for usize {}

impl sealed::Value for isize {}

impl ValueSize for usize {
    const BYTES: u64 = WORD_BYTES;
}

impl ValueSize for isize {
    const BYTES: u64 = WORD_BYTES;
}

impl sealed::Value for bool {}

impl ValueSize for bool {
    const BYTES: u64 = BOOL_BYTES;
}

impl sealed::Value for () {}

impl ValueSize for () {
    const BYTES: u64 = 0;
}

impl<T: ValueSize + sealed::Integer, const N: usize> sealed::Value for [T; N] {}

impl<T: ValueSize + sealed::Integer, const N: usize> ValueSize for [T; N] {
    const BYTES: u64 = match array_bytes(T::BYTES, N as u64) {
        Some(bytes) => bytes,
        None => panic!("model array size exceeds u64"),
    };
}

impl<T> sealed::Value for Vec<T> {}

impl<T> ValueSize for Vec<T> {
    const BYTES: u64 = 3 * WORD_BYTES;
}

impl<T: ValueSize> sealed::Value for std::sync::Arc<T> {}

impl<T: ValueSize> ValueSize for std::sync::Arc<T> {
    const BYTES: u64 = WORD_BYTES;
}

impl<T: ValueSize> sealed::Value for std::thread::JoinHandle<T> {}

impl<T: ValueSize> ValueSize for std::thread::JoinHandle<T> {
    const BYTES: u64 = WORD_BYTES;
}

impl<T: ValueSize> sealed::Value for Option<T> {}

impl<T: ValueSize> ValueSize for Option<T> {
    const BYTES: u64 = T::BYTES + BOOL_BYTES;
}

impl<T> sealed::Value for Box<T> {}

impl<T> ValueSize for Box<T> {
    const BYTES: u64 = WORD_BYTES;
}

impl<T> sealed::Value for Box<[T]> {}

impl<T> ValueSize for Box<[T]> {
    const BYTES: u64 = 2 * WORD_BYTES;
}

impl sealed::Value for Box<dyn std::any::Any + Send> {}

impl ValueSize for Box<dyn std::any::Any + Send> {
    const BYTES: u64 = 2 * WORD_BYTES;
}

impl<T> sealed::Reference for &T {}

impl<T> ReferenceSize for &T {
    const BYTES: u64 = reference_bytes(false);
}

impl<T> sealed::Reference for &mut T {}

impl<T> ReferenceSize for &mut T {
    const BYTES: u64 = reference_bytes(false);
}

impl<T> sealed::Reference for &[T] {}

impl<T> ReferenceSize for &[T] {
    const BYTES: u64 = reference_bytes(true);
}

impl<T> sealed::Reference for &mut [T] {}

impl<T> ReferenceSize for &mut [T] {
    const BYTES: u64 = reference_bytes(true);
}

impl<T: ValueSize> sealed::Value for std::sync::Mutex<T> {}

impl<T: ValueSize> ValueSize for std::sync::Mutex<T> {
    const BYTES: u64 = match verus_meter_model::mutex_bytes(T::BYTES) {
        Some(bytes) => bytes,
        None => panic!("model mutex size exceeds u64"),
    };
}

impl<T: ValueSize> sealed::Value for std::sync::MutexGuard<'_, T> {}

impl<T: ValueSize> ValueSize for std::sync::MutexGuard<'_, T> {
    const BYTES: u64 = WORD_BYTES;
}

impl<T: ValueSize> sealed::Value for std::sync::PoisonError<T> {}

impl<T: ValueSize> ValueSize for std::sync::PoisonError<T> {
    const BYTES: u64 = T::BYTES;
}

impl<T: ValueSize> sealed::Value for std::sync::TryLockError<T> {}

impl<T: ValueSize> ValueSize for std::sync::TryLockError<T> {
    const BYTES: u64 = match verus_meter_model::result_bytes(T::BYTES, 0) {
        Some(bytes) => bytes,
        None => panic!("model try-lock error size exceeds u64"),
    };
}

impl<T: ValueSize, E: ValueSize> sealed::Value for Result<T, E> {}

impl<T: ValueSize, E: ValueSize> ValueSize for Result<T, E> {
    const BYTES: u64 = match verus_meter_model::result_bytes(T::BYTES, E::BYTES) {
        Some(bytes) => bytes,
        None => panic!("model result size exceeds u64"),
    };
}
