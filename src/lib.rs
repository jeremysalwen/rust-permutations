/*
Rust permutations library

Copyright (C) 2017  Jeremy Salwen

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

//! A module for representing permutations, applying them to slices and indices,
//! and computing them from sort orders.
//!
//! Some practical uses of this module are:
//!  * Calculate a sort, and apply it later.
//!  * Calculate a sort on one vector, and apply it to another vector.
//!  * Calculate a sort on one vector, and apply it to multiple other vectors.
//!  * Calculate the new index of an element before sorting.
//!  * Remember the prior index of an element after sorting.
//!  * Undo a sort.
//!  * Compare the orderings of elements.

pub mod permutation;
pub use permutation::*;
