//! Erased allocation metadata and proved ownership-forest operations.
//!
//! Records distinguish charged bytes from reservation lower bounds. Proofs
//! compose fixed ownership paths, runtime child collections, and iteration.
//! The compiler activates broadcast groups explicitly at their use sites.
pub mod blocks;
pub mod cost;
pub mod forest;
pub mod groups;
pub mod iteration;
pub mod ranges;
pub mod removal;
pub mod selection;
pub mod views;
