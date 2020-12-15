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

use std;
use std::cmp::Ordering;
use std::ops::Deref;

#[derive(Clone, Debug)]
pub struct Permutation {
    inv: bool,
    indices: Vec<usize>,
}

impl std::cmp::PartialEq for Permutation {
    ///  This method compares two Permutations for equality, and is uses by `==`
    fn eq(&self, other: &Permutation) -> bool {
        if self.inv == other.inv {
            self.indices == other.indices
        } else {
            self.indices
                .iter()
                .enumerate()
                .all(|(i, &j)| other.indices[j] == i)
        }
    }
}
impl std::cmp::Eq for Permutation {}
impl<'a, 'b> std::ops::Mul<&'b Permutation> for &'a Permutation {
    type Output = Permutation;
    /// Multiply permutations, in the mathematical sense.
    ///
    /// Given two permutations `a`, and `b`, `a * b` is defined as
    /// the permutation created by first applying b, then applying a.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let p1 = Permutation::from_vec(vec![1, 0, 2]);
    /// let p2 = Permutation::from_vec(vec![0, 2, 1]);
    /// assert_eq!(&p1 * &p2, Permutation::from_vec(vec![2,0,1]));
    /// ```

    fn mul(self, rhs: &'b Permutation) -> Self::Output {
        match (self.inv, rhs.inv) {
            (_, false) => Permutation::from_vec(self.apply_slice(&rhs.indices[..])),
            (false, true) => return self * &(rhs * &Permutation::one(self.len())),
            (true, true) => Permutation {
                inv: true,
                indices: rhs.apply_inv_slice(&self.indices[..]),
            },
        }
    }
}

impl Permutation {
    /// Create a permutation from a vector of indices.
    ///
    /// from_vec(v) returns the permutation P such that P applied to [1,2,...,N] is v.
    /// Note that this notation is the inverse of the usual [one-line notation](https://en.wikipedia.org/wiki/Permutation#Definition_and_notations)
    /// used in mathematics.  This is a known issue and may change in a newer release.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let vec = vec!['a','b','c','d'];
    /// let permutation = Permutation::from_vec(vec![0,2,3,1]);
    /// assert_eq!(permutation.apply_slice(&vec[..]), vec!['a','c','d','b']);
    /// ```
    pub fn from_vec(vec: Vec<usize>) -> Permutation {
        let result = Permutation {
            inv: false,
            indices: vec,
        };

        debug_assert!(result.valid());
        return result;
    }
    /// Computes the permutation that would sort a given slice.
    ///
    /// This is the same as `permutation::sort()`, but assigned in-place to `self` rather than
    /// allocating a new permutation.
    ///
    /// # Panics
    ///
    /// If self.len() != vec.len()
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// // Say you have a permutation that we don't need anymore...
    /// let mut permutation = permutation::sort(&[0,1,2][..]);
    ///
    /// // You can reuse it rather than allocating a new one, as long as the length is the same
    /// let mut vec = vec!['z','w','h'];
    /// permutation.assign_from_sort(&vec[..]);
    /// let permuted = permutation.apply_slice(&vec[..]);
    /// vec.sort();
    /// assert_eq!(vec, permuted);
    ///
    /// // You can also use it to sort multiple arrays based on the ordering of one.
    /// let names = vec!["Bob", "Steve", "Jane"];
    /// let salary = vec![10, 5, 15];
    /// permutation.assign_from_sort(&salary[..]);
    /// let ordered_names = permutation.apply_slice(&names[..]);
    /// let ordered_salaries = permutation.apply_slice(&salary[..]);
    /// assert_eq!(ordered_names, vec!["Steve", "Bob", "Jane"]);
    /// assert_eq!(ordered_salaries, vec![5, 10, 15]);
    /// ```
    pub fn assign_from_sort<T, D>(&mut self, vec: D)
    where
        T: Ord,
        D: Deref<Target = [T]>,
    {
        assert_eq!(self.len(), vec.len());
        //We use the reverse permutation form, because its more efficient for applying to indices.
        self.indices.sort_by_key(|&i| &vec[i]);
    }

    /// Computes the permutation that would sort a given slice by a comparator.
    ///
    /// This is the same as `permutation::sort_by()`, but assigned in-place to `self` rather than
    /// allocating a new permutation.
    ///
    /// # Panics
    ///
    /// If self.len() != vec.len()
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// // Say you have a permutation that we don't need anymore...
    /// let mut permutation = permutation::sort(&[0,1,2,3,4,5][..]);
    ///
    /// // You can assign to it rather than allocating a new one, as long as the length is the same
    /// let mut vec = vec!['z','w','h','a','s','j'];
    /// permutation.assign_from_sort_by(&vec[..], |a, b| b.cmp(a));
    /// let permuted = permutation.apply_slice(&vec[..]);
    /// vec.sort_by(|a,b| b.cmp(a));
    /// assert_eq!(vec, permuted);
    /// ```
    pub fn assign_from_sort_by<T, D, F>(&mut self, vec: D, mut compare: F)
    where
        T: Ord,
        D: Deref<Target = [T]>,
        F: FnMut(&T, &T) -> Ordering,
    {
        assert_eq!(self.indices.len(), vec.len());
        //We use the reverse permutation form, because its more efficient for applying to indices.
        self.indices.sort_by(|&i, &j| compare(&vec[i], &vec[j]));
    }

    /// Computes the permutation that would sort a given slice by a key function.
    ///
    /// This is the same as `permutation::sort_by_key()`, but assigned in-place to `self` rather than
    /// allocating a new permutation.
    ///
    /// # Panics
    ///
    /// If self.len() != vec.len()
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// // Say you have a permutation that we don't need anymore...
    /// let mut permutation = permutation::sort(&[0,1,2,3,4,5][..]);
    ///
    /// // You can assign to it rather than allocating a new one, as long as the length is the same
    /// let mut vec = vec![2, 4, 6, 8, 10, 11];
    /// permutation.assign_from_sort_by_key(&vec[..], |a| a % 3);
    /// let permuted = permutation.apply_slice(&vec[..]);
    /// vec.sort_by_key(|a| a % 3);
    /// assert_eq!(vec, permuted);
    /// ```
    pub fn assign_from_sort_by_key<T, D, B, F>(&mut self, vec: D, mut f: F)
    where
        B: Ord,
        D: Deref<Target = [T]>,
        F: FnMut(&T) -> B,
    {
        assert_eq!(self.indices.len(), vec.len());
        //We use the reverse permutation form, because its more efficient for applying to indices.
        self.indices.sort_by_key(|&i| f(&vec[i]));
    }
    /// Return the identity permutation of size N.
    ///
    /// This returns the identity permutation of N elements.
    ///
    /// # Examples
    /// ```
    /// # use permutation::Permutation;
    /// let vec = vec!['a','b','c','d'];
    /// let permutation = Permutation::one(4);
    /// assert_eq!(permutation.apply_slice(&vec[..]), vec!['a','b','c','d']);
    /// ```
    pub fn one(len: usize) -> Permutation {
        Permutation {
            inv: false,
            indices: (0..len).collect(),
        }
    }
    /// Return the size of a permutation.
    ///
    /// This is the number of elements that the permutation acts on.
    ///
    /// # Examples
    /// ```
    /// use permutation::Permutation;
    /// let permutation = Permutation::one(4);
    /// assert_eq!(permutation.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        return self.indices.len();
    }
    /// Check whether a permutation is valid.
    ///
    /// A permutation can be invalid if it was constructed with an
    /// incorrect vector using ``::from_vec()``.  Debug assertions will
    /// catch this on construction, so it should never return true.
    ///
    pub fn valid(&self) -> bool {
        let mut sorted = self.indices.clone();
        sorted.sort();
        return sorted.iter().enumerate().all(|(i, &j)| i == j);
    }

    /// Return the inverse of a permutation.
    ///
    /// This returns a permutation that will undo a given permutation.
    /// Internally, this does not compute the inverse, but just flips a bit.
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,2,3,1]);
    /// assert_eq!(permutation.inverse(), Permutation::from_vec(vec![0,3,1,2]));
    /// ```
    pub fn inverse(mut self) -> Permutation {
        self.inv ^= true;
        return self;
    }

    /// Normalize the internal storage of the `Permutation`, optimizing it for forward or inverse application.
    ///
    /// Internally, the permutation has a bit to indicate whether it is inverted.
    /// This is because given a permutation P, it is just as easy to compute `P^-1 * Q`
    /// as it is to compute `P * Q`. However, computing the entries of `P^-1` requires some computation.
    /// However, when applying to the permutation to an index, the permutation has a "preferred" direction, which
    /// is much quicker to compute.
    ///
    /// The `normalize()` method does not change the value of the permutation, but
    /// it converts it into the preferred form for applying `P` or its inverse, respectively.
    ///
    /// If `backward` is `false`, it will be in the preferred form for applying `P`,
    /// if `backward` is `true`, it will be in the preferred form for appling `P^-1`
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0, 3, 2, 5, 1, 4]);
    /// let reversed = permutation.inverse().normalize(true);
    /// assert_eq!(reversed.apply_inv_idx(3), 1);
    /// ```
    pub fn normalize(self, backward: bool) -> Permutation {
        // Note that "reverse" index lookups are easier, so we actually
        // want reversed == true for forward normalization,
        // and reverse == false for backward normalization.
        if self.inv ^ backward {
            self
        } else {
            let len = self.len();
            if backward {
                &self * &Permutation::one(len)
            } else {
                (&self.inverse() * &Permutation::one(len)).inverse()
            }
        }
    }
    fn apply_idx_fwd(&self, idx: usize) -> usize {
        self.indices.iter().position(|&v| v == idx).unwrap()
    }
    fn apply_idx_bkwd(&self, idx: usize) -> usize {
        self.indices[idx]
    }

    /// Apply the permutation to an index.
    ///
    /// Given an index of an element, this will return the new index
    /// of that element after applying the permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,2,1]);
    /// assert_eq!(permutation.apply_idx(2), 1);
    pub fn apply_idx(&self, idx: usize) -> usize {
        match self.inv {
            false => self.apply_idx_fwd(idx),
            true => self.apply_idx_bkwd(idx),
        }
    }

    /// Apply the inverse of a permutation to an index.
    ///
    /// Given an index of an element, this will return the new index
    /// of that element after applying 'P^-1'.
    ///
    /// Equivalently, if `P.apply_idx(i) == j`, then `P.apply_inv_idx(j) == i`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,2,1]);
    /// assert_eq!(permutation.apply_inv_idx(1), 2);
    /// ```
    pub fn apply_inv_idx(&self, idx: usize) -> usize {
        match self.inv {
            true => self.apply_idx_fwd(idx),
            false => self.apply_idx_bkwd(idx),
        }
    }
    fn apply_slice_fwd<T: Clone, D>(&self, vec: D) -> Vec<T>
    where
        D: Deref<Target = [T]>,
    {
        self.indices.iter().map(|&idx| vec[idx].clone()).collect()
    }

    fn apply_slice_bkwd<T: Clone, D>(&self, vec: D) -> Vec<T>
    where
        D: Deref<Target = [T]>,
    {
        let mut other: Vec<T> = vec.to_vec();
        for (i, idx) in self.indices.iter().enumerate() {
            other[*idx] = vec[i].clone();
        }
        return other;
    }

    // For the in place methods, we apply each cycle in the permutation in turn, marking the indices with their MSB when
    // they have been resolved. The MSB will always be unset as long as n <= isize::max_value().
    // This way, we can recover the original indices in O(n) and perform no heap allocations.

    #[inline(always)]
    fn mark_idx(idx: usize) -> usize {
        idx ^ isize::min_value() as usize
    }

    #[inline(always)]
    fn idx_is_marked(idx: usize) -> bool {
        (idx & (isize::min_value() as usize)) != 0
    }

    fn apply_slice_bkwd_in_place<T>(&mut self, slice: &mut [T]) {
        for idx in self.indices.iter() {
            assert!(!Self::idx_is_marked(*idx));
        }

        for i in 0..self.indices.len() {
            let i_idx = self.indices[i];

            if Self::idx_is_marked(i_idx) {
                continue;
            }

            if i_idx == i {
                // For cycles of length 1, we don't perform any swaps
                self.indices[i] = Self::mark_idx(i_idx);
            } else {
                // For all other cycles of length n, we need n swaps
                let mut j = i;
                let mut j_idx = i_idx;
                'inner: loop {
                    slice.swap(j, j_idx);
                    self.indices[j] = Self::mark_idx(j_idx);

                    j = j_idx;
                    j_idx = self.indices[j];

                    // When we loop back to the first index, we stop
                    if j_idx == i {
                        self.indices[j] = Self::mark_idx(j_idx);
                        break 'inner;
                    }
                }
            }
        }

        for idx in self.indices.iter_mut() {
            assert!(Self::idx_is_marked(*idx));
            *idx = Self::mark_idx(*idx);
        }
    }

    /// Apply a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements according
    /// to this permutation and clone them to a `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,3,1,2]);
    /// let vec = vec!['a','b','c','d'];
    /// assert_eq!(permutation.apply_slice(&vec[..]), vec!['a', 'd', 'b', 'c']);
    /// ```
    #[must_use]
    pub fn apply_slice<T: Clone, D>(&self, vec: D) -> Vec<T>
    where
        D: Deref<Target = [T]>,
    {
        assert_eq!(vec.len(), self.len());
        match self.inv {
            false => self.apply_slice_fwd(vec),
            true => self.apply_slice_bkwd(vec),
        }
    }
    /// Apply the inverse of a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements according
    /// to the inverse of this permutation and clone them to a `Vec`.
    /// This is equivalent to "undoing" the permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,3,1,2]);
    /// let vec = vec!['a','b', 'c', 'd'];
    /// assert_eq!(permutation.apply_inv_slice(vec), vec!['a', 'c', 'd', 'b']);
    /// ```
    #[must_use]
    pub fn apply_inv_slice<T: Clone, D>(&self, vec: D) -> Vec<T>
    where
        D: Deref<Target = [T]>,
    {
        assert_eq!(vec.len(), self.len());
        match self.inv {
            false => self.apply_slice_bkwd(vec),
            true => self.apply_slice_fwd(vec),
        }
    }

    /// Apply a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements in place according
    /// to this permutation.
    ///
    /// This method borrows `self` mutably to avoid allocations, but the permutation
    /// will be unchanged after it returns.
    ///
    /// Note that unlike the other `apply_*` methods, this method *requires* the permutation
    /// to be normalized in the opposite direction, or it will panic.
    ///
    /// # Panics
    ///
    /// If the permutation is not normalized for backward application.
    /// If `slice.len() != self.len()`.
    /// If `slice.len()` > isize::max_value(), due to implementation reasons.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let mut permutation = Permutation::from_vec(vec![0,3,1,2]);
    /// let mut vec = vec!['a', 'b', 'c', 'd'];
    /// let permutation_old = permutation.clone();
    /// permutation.apply_slice_in_place(vec.as_mut_slice());
    /// assert_eq!(vec, vec!['a', 'd', 'b', 'c']);
    /// ```
    pub fn apply_slice_in_place<T>(&mut self, slice: &mut [T]) {
        assert_eq!(slice.len(), self.len());
        match self.inv {
            false => self.apply_slice_bkwd_in_place(slice),
            true => panic!("Permutation not normalized for backward application"),
        }
    }

    /// Apply the inverse of a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements in placeaccording
    /// to the inverse of this permutation.
    /// This is equivalent to "undoing" the permutation.
    ///
    /// This method borrows `self` mutably to avoid allocations, but the permutation
    /// will be unchanged after it returns.
    ///
    /// # Panics
    ///
    /// If the permutation is not normalized for forward application.
    /// If `slice.len() != self.len()`.
    /// If `slice.len()` > isize::max_value(), due to implementation reasons.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let mut permutation = Permutation::from_vec(vec![0,3,1,2]).normalize(false);
    /// let mut vec = vec!['a', 'b', 'c', 'd'];
    /// permutation.apply_inv_slice_in_place(vec.as_mut_slice());
    /// assert_eq!(vec, vec!['a', 'c', 'd', 'b']);
    /// ```
    pub fn apply_inv_slice_in_place<T>(&mut self, slice: &mut [T]) {
        assert_eq!(slice.len(), self.len());
        assert!(slice.len() <= isize::max_value() as usize);

        match self.inv {
            false => panic!("Permutation not normalized for forward application"),
            true => self.apply_slice_bkwd_in_place(slice),
        }
    }
}
/// Return the permutation that would sort a given slice.
///
/// This calculates the permutation that if it were applied to the slice,
/// would put the elements in sorted order.
///
/// # Examples
///
/// ```
/// # use permutation::Permutation;
/// let mut vec = vec!['z','w','h','a','s','j'];
/// let permutation = permutation::sort(&vec[..]);
/// let permuted = permutation.apply_slice(&vec[..]);
/// vec.sort();
/// assert_eq!(vec, permuted);
/// ```
///
/// You can also use it to sort multiple arrays based on the ordering of one.
///
/// ```
/// let names = vec!["Bob", "Steve", "Jane"];
/// let salary = vec![10, 5, 15];
/// let permutation = permutation::sort(&salary[..]);
/// let ordered_names = permutation.apply_slice(&names[..]);
/// let ordered_salaries = permutation.apply_slice(&salary[..]);
/// assert_eq!(ordered_names, vec!["Steve", "Bob", "Jane"]);
/// assert_eq!(ordered_salaries, vec![5, 10, 15]);
/// ```
pub fn sort<T, D>(vec: D) -> Permutation
where
    T: Ord,
    D: Deref<Target = [T]>,
{
    let mut permutation = Permutation::one(vec.len());
    //We use the reverse permutation form, because its more efficient for applying to indices.
    permutation.indices.sort_by_key(|&i| &vec[i]);
    return permutation;
}

/// Return the permutation that would sort a given slice by a comparator.
///
/// This is the same as `permutation::sort()` except that it allows you to specify
/// the comparator to use when sorting similar to `std::slice.sort_by()`
///
/// # Examples
///
/// ```
/// # use permutation::Permutation;
/// let mut vec = vec!['z','w','h','a','s','j'];
/// let permutation = permutation::sort_by(&vec[..], |a, b| b.cmp(a));
/// let permuted = permutation.apply_slice(&vec[..]);
/// vec.sort_by(|a,b| b.cmp(a));
/// assert_eq!(vec, permuted);
/// ```
pub fn sort_by<T, D, F>(vec: D, mut compare: F) -> Permutation
where
    T: Ord,
    D: Deref<Target = [T]>,
    F: FnMut(&T, &T) -> Ordering,
{
    let mut permutation = Permutation::one(vec.len());
    //We use the reverse permutation form, because its more efficient for applying to indices.
    permutation
        .indices
        .sort_by(|&i, &j| compare(&vec[i], &vec[j]));
    return permutation;
}

/// Return the permutation that would sort a given slice by a key function.
///
/// This is the same as `permutation::sort()` except that it allows you to specify
/// the key function simliar to `std::slice.sort_by_key()`
///
/// # Examples
///
/// ```
/// # use permutation::Permutation;
/// let mut vec = vec![2, 4, 6, 8, 10, 11];
/// let permutation = permutation::sort_by_key(&vec[..], |a| a % 3);
/// let permuted = permutation.apply_slice(&vec[..]);
/// vec.sort_by_key(|a| a % 3);
/// assert_eq!(vec, permuted);
/// ```
pub fn sort_by_key<T, D, B, F>(vec: D, mut f: F) -> Permutation
where
    B: Ord,
    D: Deref<Target = [T]>,
    F: FnMut(&T) -> B,
{
    let mut permutation = Permutation::one(vec.len());
    //We use the reverse permutation form, because its more efficient for applying to indices.
    permutation.indices.sort_by_key(|&i| f(&vec[i]));
    return permutation;
}

#[cfg(test)]
mod tests {
    use permutation;
    use permutation::Permutation;

    #[test]
    fn basics() {
        let p1 = Permutation::one(5);
        let p2 = Permutation::one(5);
        assert!(p1.valid());
        assert_eq!(p1, p2);
        let p3 = Permutation::one(6);
        assert!(p1 != p3);

        assert_eq!(&p1 * &p2, p1);
        assert_eq!(p1.clone().inverse(), p1);
    }

    #[test]
    fn powers() {
        let id = Permutation::one(3);
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let square = &p1 * &p1;
        assert_eq!(square, id);
        let cube = &p1 * &square;
        assert_eq!(cube, p1);
    }
    #[test]
    fn prod() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let p2 = Permutation::from_vec(vec![0, 2, 1]);
        let prod = &p1 * &p2;
        assert_eq!(prod, Permutation::from_vec(vec![2, 0, 1]));
    }
    #[test]
    fn len() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        assert_eq!(p1.len(), 3)
    }
    fn check_not_equal_inverses(p2: &Permutation, p3: &Permutation) {
        assert!(*p2 != *p3);
        assert_eq!(p2 * p3, Permutation::one(p2.len()));
        assert_eq!(p3 * p2, Permutation::one(p2.len()));
        assert_eq!(*p2, p3.clone().inverse());
        assert_eq!(p2.clone().inverse(), *p3);
        assert!(p2.clone().inverse() != p3.clone().inverse());
        assert!(p2 * &p3.clone().inverse() != Permutation::one(p2.len()));
        assert!(&p2.clone().inverse() * p3 != Permutation::one(p2.len()));
    }
    #[test]
    fn inverse() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let rev = p1.clone().inverse();
        assert_eq!(p1, rev);

        //An element and its inverse
        let p2 = Permutation::from_vec(vec![1, 2, 0, 4, 3]);
        let p3 = Permutation::from_vec(vec![2, 0, 1, 4, 3]);

        check_not_equal_inverses(&p2, &p3);
        println!(
            "{:?}, {:?}, {:?}",
            p2.clone().inverse(),
            p3.clone().inverse(),
            &p2.clone().inverse() * &p3.clone().inverse()
        );
        assert_eq!(
            &p2.clone().inverse() * &p3.clone().inverse(),
            Permutation::one(p2.len())
        );

        //An element, and a distinct element which is not its inverse.
        let p4 = Permutation::from_vec(vec![1, 2, 0, 3, 4]);
        let p5 = Permutation::from_vec(vec![2, 0, 1, 4, 3]);

        assert!(p4 != p5);
        assert!(p4 != p5.clone().inverse());
        assert!(p4.clone().inverse() != p5);
        assert!(p4.clone().inverse() != p5.clone().inverse());
        assert!(&p4 * &p5 != Permutation::one(p4.len()));
        assert!(&p5 * &p4 != Permutation::one(p4.len()));
        assert!(&p4.clone().inverse() * &p5 != Permutation::one(p4.len()));
        assert!(&p4 * &p5.clone().inverse() != Permutation::one(p4.len()));
    }

    #[test]
    fn sorting() {
        let elems = vec!['a', 'b', 'e', 'g', 'f'];
        let perm = permutation::sort(&elems[..]);
        println!("{:?}", perm);
        assert_eq!(perm, Permutation::from_vec(vec![0, 1, 2, 4, 3]));
    }
    #[test]
    fn strings() {
        let elems = vec!["doggie", "cat", "doggo", "dog", "doggies", "god"];
        let perm = permutation::sort(&elems[..]);
        assert_eq!(perm, Permutation::from_vec(vec![1, 3, 0, 4, 2, 5]));

        assert!(
            perm.apply_slice(&elems[..]) == vec!["cat", "dog", "doggie", "doggies", "doggo", "god"]
        );
        let parallel = vec!["doggie1", "cat1", "doggo1", "dog1", "doggies1", "god1"];
        let par_permuted = perm.apply_slice(&parallel[..]);
        println!("{:?}", par_permuted);
        assert_eq!(
            par_permuted,
            vec!["cat1", "dog1", "doggie1", "doggies1", "doggo1", "god1"]
        );
        assert_eq!(perm.apply_inv_slice(par_permuted), parallel);
    }

    #[test]
    fn by_key() {
        let vec = vec![1, 10, 9, 8];
        let perm = permutation::sort_by_key(vec, |i| -i);
        assert_eq!(perm, Permutation::from_vec(vec![1, 2, 3, 0]));
    }

    #[test]
    fn by_cmp() {
        let vec = vec!["aaabaab", "aba", "cas", "aaab"];
        let perm = permutation::sort_by(vec, |a, b| a.cmp(b));
        assert_eq!(perm, Permutation::from_vec(vec![3, 0, 1, 2]));
    }

    #[test]
    fn indices() {
        let vec = vec![100, 10, 1, 1000];
        let perm = permutation::sort_by_key(vec, |x| -x);
        println!("{:?}", perm.apply_inv_idx(0));
        assert_eq!(perm.apply_inv_idx(0), 3);
        assert_eq!(perm.apply_idx(3), 0);

        assert_eq!(perm.apply_inv_idx(1), 0);
        assert_eq!(perm.apply_idx(0), 1);

        assert_eq!(perm.apply_inv_idx(2), 1);
        assert_eq!(perm.apply_idx(1), 2);

        assert_eq!(perm.apply_inv_idx(3), 2);
        assert_eq!(perm.apply_idx(2), 3);
    }
    #[test]
    fn normalize() {
        let vec = vec![100, 10, 1, 1000];
        let perm = permutation::sort_by_key(vec, |x| -x);
        let f = perm.clone().normalize(false);
        let b = perm.clone().normalize(true);
        assert_eq!(perm, f);
        assert_eq!(f, b);
        for idx in 0..perm.len() {
            assert_eq!(perm.apply_idx(idx), f.apply_idx(idx));
            assert_eq!(f.apply_idx(idx), b.apply_idx(idx));
            assert_eq!(perm.apply_inv_idx(idx), f.apply_inv_idx(idx));
            assert_eq!(f.apply_inv_idx(idx), b.apply_inv_idx(idx));
        }
        let inv = perm.clone().inverse();
        let fi = inv.clone().normalize(false);
        let bi = inv.clone().normalize(true);
        assert_eq!(inv, fi);
        assert_eq!(fi, bi);
        for idx in 0..perm.len() {
            assert_eq!(inv.apply_idx(idx), fi.apply_idx(idx));
            assert_eq!(fi.apply_idx(idx), bi.apply_idx(idx));
            assert_eq!(inv.apply_inv_idx(idx), fi.apply_inv_idx(idx));
            assert_eq!(fi.apply_inv_idx(idx), bi.apply_inv_idx(idx));
        }
    }
    #[test]
    fn normalize_inv() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let rev = p1.clone().inverse();
        assert_eq!(p1, rev);

        //An element and its inverse
        let mut p2 = Permutation::from_vec(vec![1, 2, 0, 4, 3]);
        let mut p3 = Permutation::from_vec(vec![2, 0, 1, 4, 3]);

        p2 = p2.normalize(false);
        p3 = p3.normalize(false);
        check_not_equal_inverses(&p2, &p3);

        p2 = p2.normalize(true);
        p3 = p3.normalize(true);
        check_not_equal_inverses(&p2, &p3);

        p2 = p2.normalize(true);
        p3 = p3.normalize(false);
        check_not_equal_inverses(&p2, &p3);

        p2 = p2.normalize(false);
        p3 = p3.normalize(true);
        check_not_equal_inverses(&p2, &p3);
    }

    #[test]
    fn apply_in_place() {
        let mut p = Permutation::from_vec(vec![2, 0, 1, 4, 3]);
        let p_old = p.clone();

        let mut vec = vec!['a', 'b', 'c', 'd', 'e'];

        p.apply_slice_in_place(vec.as_mut_slice());

        assert_eq!(vec, vec!['c', 'a', 'b', 'e', 'd']);
        assert_eq!(p.indices, p_old.indices);
        assert_eq!(p.inv, p_old.inv);
    }

    #[test]
    fn apply_inv_in_place() {
        let mut p = Permutation::from_vec(vec![2, 0, 1, 4, 3])
            .inverse()
            .normalize(true);
        let p_old = p.clone();

        let mut vec = vec!['c', 'a', 'b', 'e', 'd'];

        p.apply_slice_in_place(vec.as_mut_slice());

        assert_eq!(vec, vec!['a', 'b', 'c', 'd', 'e']);
        assert_eq!(p.indices, p_old.indices);
        assert_eq!(p.inv, p_old.inv);
    }
}
