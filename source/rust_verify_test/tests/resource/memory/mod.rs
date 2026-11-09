//! Memory contract verification, grouped by the behavior being checked.

mod array_copy;
mod borrowed_vectors;
mod call_budgets;
mod call_graph;
mod checkpoints;
mod conditional;
mod growth;
mod heap;
mod integers;
mod lifetimes;
mod ownership;
mod reachability;
mod return_sharing;
mod returns;
mod sections;
mod spec_functions;
mod storage;
mod storage_budgets;
mod storage_calls;
mod storage_initialization;
mod storage_model;
mod storage_slices;
mod storage_structs;
mod vectors;

mod support;
