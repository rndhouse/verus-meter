//! Translate memory contracts and identify operations used by the memory model.

pub(crate) mod budget;
mod cleanup;
pub(crate) mod concurrency;
pub(crate) mod intrinsics;
pub(crate) mod pipeline;
