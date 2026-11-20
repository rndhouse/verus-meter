//! Shared source-storage policy, independent of compiler and executable ABI layout.
#![no_std]

/// Word size in the current 64-bit source model.
pub const WORD_BYTES: u64 = 8;
/// Boolean storage in the source model.
pub const BOOL_BYTES: u64 = 1;

/// Native integer storage for the widths supported by the memory checker.
pub const fn integer_bytes(bits: u32) -> Option<u64> {
    match bits {
        8 | 16 | 32 | 64 | 128 => Some((bits / 8) as u64),
        _ => None,
    }
}

/// Checked inline storage for a fixed integer array.
pub const fn array_bytes(element: u64, count: u64) -> Option<u64> {
    element.checked_mul(count)
}

/// Storage of a reference handle, excluding its pointee.
pub const fn reference_bytes(slice: bool) -> u64 {
    if slice { 2 * WORD_BYTES } else { WORD_BYTES }
}

/// Storage of the cursor and end of a shared forward slice iterator.
pub const SLICE_ITERATOR_BYTES: u64 = 2 * WORD_BYTES;

/// State live in the body of a lowered `for item in source` shared traversal.
/// The lowering keeps its initial source reference, the wrapped iterator, the
/// yielded reference and its copy in the user's item binding.
pub const fn borrowed_for_loop_bytes(source_is_slice: bool) -> u64 {
    reference_bytes(source_is_slice) + SLICE_ITERATOR_BYTES + 2 * reference_bytes(false)
}

/// Inline mutex source storage: synchronization state, poison flag and payload.
/// This describes source storage, not the platform lock ABI or OS workspace.
pub const fn mutex_bytes(payload: u64) -> Option<u64> {
    match payload.checked_add(WORD_BYTES) {
        Some(bytes) => bytes.checked_add(BOOL_BYTES),
        None => None,
    }
}

/// Inline variant tag plus the larger Result payload; allocations stay separate.
pub const fn result_bytes(ok: u64, err: u64) -> Option<u64> {
    let payload = if ok > err { ok } else { err };
    payload.checked_add(BOOL_BYTES)
}

/// Shared backing contains two source count words and the inline payload.
/// Handle bytes and payload-owned descendant allocations are separate charges.
pub const fn arc_backing_bytes(payload: u64) -> Option<u64> {
    payload.checked_add(2 * WORD_BYTES)
}

/// A completion starts with its state tag and acquires inline result storage
/// only when the worker produces its result. Descendant allocations stay separate.
pub const fn completion_bytes(result: u64) -> Option<u64> {
    result.checked_add(BOOL_BYTES)
}
