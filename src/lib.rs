//! A module for representing permutations, applying them to slices and indices,
//! and computing them from sort orders.
//!
//! Some practical uses of this module are:
//!
//!  * Calculate a sort, and apply it later.
//!  * Calculate a sort on one vector, and apply it to another vector.
//!  * Calculate a sort on one vector, and apply it to multiple other vectors.
//!  * Calculate the new index of an element before sorting.
//!  * Remember the prior index of an element after sorting.
//!  * Undo a sort.
//!  * Compare the orderings of elements.

pub mod permutation;
pub use permutation::*;
