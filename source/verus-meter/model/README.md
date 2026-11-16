# Shared storage policy

This crate contains the fixed word size and primitive sizing operations shared by
the verifier's memory layouts and runtime-query size traits. It has no compiler,
solver, allocator, or ABI-layout dependencies. Layout eligibility, ownership, and
resource obligations remain in the verifier; typed expression interpretation stays
in the runtime crate. Sharing these definitions does not expand either component's
supported types automatically.
