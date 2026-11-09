//! Facts derived together while checking a function, consumed together at calls.

/// Call-composition facts established together by a checked function body.
#[derive(Clone)]
pub(super) struct FunctionSummary {
    /// Container-independent ownership, byte sizes, and retained replacements.
    pub(super) allocations: super::allocations::AllocationSummary,
    /// Vector-specific reservation requirements and result capacity facts.
    pub(super) vectors: super::vector_calls::VectorSummary,
    /// Zero-based input index when the result forwards that value's charge.
    pub(super) return_parameter: Option<usize>,
    /// Simultaneous costs and input/result lifetimes needed to compose a call.
    pub(super) profiles: Vec<super::lifetime::Profile>,
}
