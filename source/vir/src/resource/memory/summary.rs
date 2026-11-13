//! Facts derived together while checking a function, consumed together at calls.

/// Call-composition facts established together by a checked function body.
#[derive(Clone)]
pub(super) struct FunctionSummary {
    /// Borrowed owner roots changed by checked operations, including logical
    /// length changes that retain the same allocation and reservation.
    pub(super) modified_parameters: std::collections::BTreeSet<usize>,
    /// Physical-ownership transformation, required for runtime ownership interfaces.
    pub(super) transfer: Option<super::transfer::Template>,
    /// Owning runtime operations require this interface even behind leaf returns.
    pub(super) transfer_required: bool,
    /// Container-independent ownership, byte sizes, and retained replacements.
    pub(super) allocations: super::allocations::AllocationSummary,
    /// Vector-specific reservation requirements and result capacity facts.
    pub(super) vectors: super::vector_calls::VectorSummary,
    /// Allocation provenance IDs map to disjoint nodes of owned parameter trees.
    pub(super) input_paths: Vec<super::paths::InputPath>,
    /// Zero-based input index when the result forwards that value's charge.
    pub(super) return_parameter: Option<usize>,
    /// Simultaneous costs and input/result lifetimes needed to compose a call.
    pub(super) profiles: Vec<super::lifetime::Profile>,
}
