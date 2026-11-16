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
