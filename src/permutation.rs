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

#[derive(Clone,Debug)]
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
    /// assert!(&p1 * &p2 == Permutation::from_vec(vec![2,0,1]));
    /// ```

    fn mul(self, rhs: &'b Permutation) -> Self::Output {
        match (self.inv, rhs.inv) {
            (_, false) => Permutation::from_vec(self.apply_slice(&rhs.indices[..])),
            (false, true) => return self * &(rhs * &Permutation::one(self.len())),
            (true, true) => {
                Permutation {
                    inv: true,
                    indices: rhs.apply_inv_slice(&self.indices[..]),
                }
            }
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
    /// assert!(permutation.apply_slice(&vec[..]) == vec!['a','c','d','b']);
    /// ```
    pub fn from_vec(vec: Vec<usize>) -> Permutation {
        let result = Permutation {
            inv: false,
            indices: vec,
        };

        debug_assert!(result.valid());
        return result;
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
    /// assert!(permutation.apply_slice(&vec[..]) == vec!['a','b','c','d']);
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
    /// assert!(permutation.len() == 4);
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
    /// assert!(permutation.inverse() == Permutation::from_vec(vec![0,3,1,2]));
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
    /// assert!(reversed.apply_inv_idx(3) == 1);
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
        self.indices
            .iter()
            .position(|&v| v == idx)
            .unwrap()
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
    /// assert!(permutation.apply_idx(2) == 1);
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
    /// assert!(permutation.apply_inv_idx(1) == 2);
    /// ```
    pub fn apply_inv_idx(&self, idx: usize) -> usize {
        match self.inv {
            true => self.apply_idx_fwd(idx),
            false => self.apply_idx_bkwd(idx),
        }
    }
    fn apply_slice_fwd<T: Clone, D>(&self, vec: D) -> Vec<T>
        where D: Deref<Target = [T]>
    {
        self.indices
            .iter()
            .map(|&idx| vec[idx].clone())
            .collect()
    }

    fn apply_slice_bkwd<T: Clone, D>(&self, vec: D) -> Vec<T>
        where D: Deref<Target = [T]>
    {
        let mut other: Vec<T> = vec.to_vec();
        for (i, idx) in self.indices.iter().enumerate() {
            other[*idx] = vec[i].clone();
        }
        return other;
    }
    /// Apply a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements in place according
    /// to this permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,3,1,2]);
    /// let vec = vec!['a','b','c','d'];
    /// assert!(permutation.apply_slice(&vec[..]) == vec!['a', 'd', 'b', 'c']);
    /// ```
    pub fn apply_slice<T: Clone, D>(&self, vec: D) -> Vec<T>
        where D: Deref<Target = [T]>
    {
        assert!(vec.len() == self.len());
        match self.inv {
            false => self.apply_slice_fwd(vec),
            true => self.apply_slice_bkwd(vec),
        }
    }

    /// Apply the inverse of a permutation to a slice of elements
    ///
    /// Given a slice of elements, this will permute the elements in place according
    /// to the inverse of this permutation.  This is equivalent to "undoing" the permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use permutation::Permutation;
    /// let permutation = Permutation::from_vec(vec![0,3,1,2]);
    /// let vec = vec!['a','b', 'c', 'd'];
    /// assert!(permutation.apply_inv_slice(vec) == vec!['a', 'c', 'd', 'b']);
    /// ```
    pub fn apply_inv_slice<T: Clone, D>(&self, vec: D) -> Vec<T>
        where D: Deref<Target = [T]>
    {
        assert!(vec.len() == self.len());
        match self.inv {
            false => self.apply_slice_bkwd(vec),
            true => self.apply_slice_fwd(vec),
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
/// assert!(vec == permuted);
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
/// assert!(ordered_names == vec!["Steve", "Bob", "Jane"]);
/// assert!(ordered_salaries == vec![5, 10, 15]);
/// ```
pub fn sort<T, D>(vec: D) -> Permutation
    where T: Ord,
          D: Deref<Target = [T]>
{
    let mut permutation = Permutation::one(vec.len());
    //We use the reverse permutation form, because its more efficient for applying to indices.
    permutation.indices.sort_by_key(|&i| &vec[i]);
    return permutation;
}

/// Return the permutation that would sort a given slice by a comparator.
///
/// This is the same as `permutation::sort()` except that it allows you to specify
/// the comparator to use when sorting similar to `std::slice.sort_by()`.
///
/// If the comparator does not define a total ordering, the order of the elements is unspecified.
/// Per the [Rust Docs](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort_by),
/// an order is a total order if it is (for all `a`, `b` and `c`):
///
/// * total and antisymmetric: exactly one of `a < b`, `a == b` or `a > b` is true, and
/// * transitive, `a < b` and `b < c` implies `a < c`. The same must hold for both `==` and `>`.
///
/// # Examples
///
/// ```
/// # use permutation::Permutation;
/// let mut vec = vec!['z','w','h','a','s','j'];
/// let permutation = permutation::sort_by(&vec[..], |a, b| b.cmp(a));
/// let permuted = permutation.apply_slice(&vec[..]);
/// vec.sort_by(|a,b| b.cmp(a));
/// assert!(vec == permuted);
/// ```
pub fn sort_by<T, D, F>(vec: D, mut compare: F) -> Permutation
    where D: Deref<Target = [T]>,
          F: FnMut(&T, &T) -> Ordering
{
    let mut permutation = Permutation::one(vec.len());
    //We use the reverse permutation form, because its more efficient for applying to indices.
    permutation.indices.sort_by(|&i, &j| compare(&vec[i], &vec[j]));
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
/// assert!(vec == permuted);
/// ```
pub fn sort_by_key<T, D, B, F>(vec: D, mut f: F) -> Permutation
    where B: Ord,
          D: Deref<Target = [T]>,
          F: FnMut(&T) -> B
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
        assert!(p1 == p2);
        let p3 = Permutation::one(6);
        assert!(p1 != p3);

        assert!(&p1 * &p2 == p1);
        assert!(p1.clone().inverse() == p1);
    }

    #[test]
    fn powers() {
        let id = Permutation::one(3);
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let square = &p1 * &p1;
        assert!(square == id);
        let cube = &p1 * &square;
        assert!(cube == p1);
    }
    #[test]
    fn prod() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let p2 = Permutation::from_vec(vec![0, 2, 1]);
        let prod = &p1 * &p2;
        assert!(prod == Permutation::from_vec(vec![2, 0, 1]));
    }
    #[test]
    fn len() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        assert!(p1.len() == 3)
    }
    fn check_not_equal_inverses(p2: &Permutation, p3: &Permutation) {
        assert!(*p2 != *p3);
        assert!(p2 * p3 == Permutation::one(p2.len()));
        assert!(p3 * p2 == Permutation::one(p2.len()));
        assert!(*p2 == p3.clone().inverse());
        assert!(p2.clone().inverse() == *p3);
        assert!(p2.clone().inverse() != p3.clone().inverse());
        assert!(p2 * &p3.clone().inverse() != Permutation::one(p2.len()));
        assert!(&p2.clone().inverse() * p3 != Permutation::one(p2.len()));
    }
    #[test]
    fn inverse() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let rev = p1.clone().inverse();
        assert!(p1 == rev);

        //An element and its inverse
        let p2 = Permutation::from_vec(vec![1, 2, 0, 4, 3]);
        let p3 = Permutation::from_vec(vec![2, 0, 1, 4, 3]);

        check_not_equal_inverses(&p2, &p3);
        println!("{:?}, {:?}, {:?}",
                 p2.clone().inverse(),
                 p3.clone().inverse(),
                 &p2.clone().inverse() * &p3.clone().inverse());
        assert!(&p2.clone().inverse() * &p3.clone().inverse() == Permutation::one(p2.len()));

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
        assert!(perm == Permutation::from_vec(vec![0, 1, 2, 4, 3]));
    }
    #[test]
    fn strings() {
        let elems = vec!["doggie", "cat", "doggo", "dog", "doggies", "god"];
        let perm = permutation::sort(&elems[..]);
        assert!(perm == Permutation::from_vec(vec![1, 3, 0, 4, 2, 5]));

        assert!(perm.apply_slice(&elems[..]) ==
                vec!["cat", "dog", "doggie", "doggies", "doggo", "god"]);
        let parallel = vec!["doggie1", "cat1", "doggo1", "dog1", "doggies1", "god1"];
        let par_permuted = perm.apply_slice(&parallel[..]);
        println!("{:?}", par_permuted);
        assert!(par_permuted == vec!["cat1", "dog1", "doggie1", "doggies1", "doggo1", "god1"]);
        assert!(perm.apply_inv_slice(par_permuted) == parallel);
    }


    #[test]
    fn by_key() {
        let vec = vec![1, 10, 9, 8];
        let perm = permutation::sort_by_key(vec, |i| -i);
        assert!(perm == Permutation::from_vec(vec![1, 2, 3, 0]));
    }

    #[test]
    fn by_cmp() {
        let vec = vec!["aaabaab", "aba", "cas", "aaab"];
        let perm = permutation::sort_by(vec, |a, b| a.cmp(b));
        assert!(perm == Permutation::from_vec(vec![3, 0, 1, 2]));
    }

    #[test]
    fn by_partially_ordered_cmp() {
        let vec = vec![1.0, 5.0, 3.0, 2.0, 8.0];
        let perm = permutation::sort_by(vec, |a, b| a.partial_cmp(b).unwrap());
        assert!(perm == Permutation::from_vec(vec![0, 3, 2, 1, 4]));
    }

    #[test]
    fn indices() {
        let vec = vec![100, 10, 1, 1000];
        let perm = permutation::sort_by_key(vec, |x| -x);
        println!("{:?}", perm.apply_inv_idx(0));
        assert!(perm.apply_inv_idx(0) == 3);
        assert!(perm.apply_idx(3) == 0);

        assert!(perm.apply_inv_idx(1) == 0);
        assert!(perm.apply_idx(0) == 1);

        assert!(perm.apply_inv_idx(2) == 1);
        assert!(perm.apply_idx(1) == 2);

        assert!(perm.apply_inv_idx(3) == 2);
        assert!(perm.apply_idx(2) == 3);
    }
    #[test]
    fn normalize() {
        let vec = vec![100, 10, 1, 1000];
        let perm = permutation::sort_by_key(vec, |x| -x);
        let f = perm.clone().normalize(false);
        let b = perm.clone().normalize(true);
        assert!(perm == f);
        assert!(f == b);
        for idx in 0..perm.len() {
            assert!(perm.apply_idx(idx) == f.apply_idx(idx));
            assert!(f.apply_idx(idx) == b.apply_idx(idx));
            assert!(perm.apply_inv_idx(idx) == f.apply_inv_idx(idx));
            assert!(f.apply_inv_idx(idx) == b.apply_inv_idx(idx));
        }
        let inv = perm.clone().inverse();
        let fi = inv.clone().normalize(false);
        let bi = inv.clone().normalize(true);
        assert!(inv == fi);
        assert!(fi == bi);
        for idx in 0..perm.len() {
            assert!(inv.apply_idx(idx) == fi.apply_idx(idx));
            assert!(fi.apply_idx(idx) == bi.apply_idx(idx));
            assert!(inv.apply_inv_idx(idx) == fi.apply_inv_idx(idx));
            assert!(fi.apply_inv_idx(idx) == bi.apply_inv_idx(idx));
        }
    }
    #[test]
    fn normalize_inv() {
        let p1 = Permutation::from_vec(vec![1, 0, 2]);
        let rev = p1.clone().inverse();
        assert!(p1 == rev);

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
}
