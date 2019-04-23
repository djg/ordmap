use super::map::{Keys, OrdMap};

use std::borrow::Borrow;
use std::fmt;
use std::iter::{Chain, DoubleEndedIterator, FromIterator};
use std::ops::{BitOr, Sub};

#[derive(Clone)]
pub struct OrdSet<K> {
    map: OrdMap<K, ()>,
}

impl<K: Ord> OrdSet<K> {
    /// Creates an empty OrdSet.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let mut set: OrdSet<i32> = OrdSet::new();
    /// ```
    #[inline]

    pub fn new() -> OrdSet<K> {
        OrdSet { map: OrdMap::new() }
    }

    /// Creates an empty OrdSet with space for at least `n` elements in
    /// the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let mut set: OrdSet<i32> = OrdSet::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> OrdSet<K> {
        OrdSet {
            map: OrdMap::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;;
    /// let set: OrdSet<i32> = OrdSet::with_capacity(100);
    /// assert!(set.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `OrdSet`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let mut set: OrdSet<i32> = OrdSet::new();
    /// set.reserve(10);
    /// ```

    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional)
    }

    /// An iterator visiting all elements in order defined by `T: Ord`.
    /// Iterator element type is &'a T.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let mut set = OrdSet::new();
    /// set.insert("c");
    /// set.insert("a");
    /// set.insert("b");
    ///
    /// // Iteration order is sorted.
    /// for (a, b) in set.iter().zip(&["a", "b", "c"]) {
    ///     assert_eq!(a, b);
    /// }
    /// ```

    pub fn iter(&self) -> Iter<K> {
        Iter {
            iter: self.map.keys(),
        }
    }

    /// Visit the values representing the difference.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let a: OrdSet<_> = [1, 2, 3].iter().cloned().collect();
    /// let b: OrdSet<_> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{}", x); // Print 1
    /// }
    ///
    /// let diff: OrdSet<_> = a.difference(&b).cloned().collect();
    /// assert_eq!(diff, [1].iter().cloned().collect());
    ///
    /// // Note that difference is not symmetric,
    /// // and `b - a` means something else:
    /// let diff: OrdSet<_> = b.difference(&a).cloned().collect();
    /// assert_eq!(diff, [4].iter().cloned().collect());
    /// ```

    pub fn difference<'a>(&'a self, other: &'a OrdSet<K>) -> Difference<'a, K> {
        Difference {
            iter: self.iter(),
            other,
        }
    }

    /// Visit the values representing the union.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let a: OrdSet<_> = [1, 2, 3].iter().cloned().collect();
    /// let b: OrdSet<_> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order.
    /// for x in a.union(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let union: OrdSet<_> = a.union(&b).cloned().collect();
    /// assert_eq!(union, [1, 2, 3, 4].iter().cloned().collect());
    /// ```

    pub fn union<'a>(&'a self, other: &'a OrdSet<K>) -> Union<'a, K> {
        Union {
            iter: self.iter().chain(other.difference(self)),
        }
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let mut v = OrdSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let mut v = OrdSet::new();
    /// assert!(v.is_empty());
    /// v.insert(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns `true` if the set contains a value.
    ///
    /// The value may be any borrowed form of the set's value type, but
    /// `Eq` on the borrowed form *must* match those for
    /// the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let set: OrdSet<_> = [1, 2, 3].iter().cloned().collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.contains_key(value)
    }

    /// Returns `true` if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let a: OrdSet<_> = [1, 2, 3].iter().cloned().collect();
    /// let mut b = OrdSet::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint(&self, other: &OrdSet<K>) -> bool {
        self.iter().all(|v| !other.contains(v))
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have a value present, `true` is returned.
    ///
    /// If the set did have this key present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let mut set = OrdSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, key: K) -> bool {
        self.map.insert(key, ()).is_none()
    }

    /// Removes a value from the set. Returns `true` if the value was
    /// present in the set.
    ///
    /// The value may be any borrowed form of the set's value type, but
    /// `Ord` on the borrowed form *must* match those for
    /// the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let mut set = OrdSet::new();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.map.remove(value).is_some()
    }
}

impl<K> PartialEq for OrdSet<K>
where
    K: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<K> Eq for OrdSet<K> where K: Eq {}

impl<K> fmt::Debug for OrdSet<K>
where
    K: Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<K: Ord> FromIterator<K> for OrdSet<K> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> OrdSet<K> {
        let mut set = OrdSet::new();
        set.extend(iter);
        set
    }
}

impl<K: Ord> Extend<K> for OrdSet<K> {
    fn extend<I: IntoIterator<Item = K>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        let required = iter.size_hint().0;
        let reserve = self.capacity() - self.len();
        if reserve < required {
            self.reserve(required - reserve);
        }
        for k in iter {
            self.insert(k);
        }
    }
}

impl<K: Ord> Default for OrdSet<K> {
    fn default() -> Self {
        OrdSet::new()
    }
}

impl<'a, 'b, K> BitOr<&'b OrdSet<K>> for &'a OrdSet<K>
where
    K: Ord + Clone,
{
    type Output = OrdSet<K>;

    /// Returns the union of `self` and `rhs` as a new `OrdSet<K>`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate ordmap;
    /// use ordmap::OrdSet;
    ///
    /// let a: OrdSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: OrdSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set = &a | &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3, 4, 5];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitor(self, rhs: &OrdSet<K>) -> OrdSet<K> {
        self.union(rhs).cloned().collect()
    }
}

impl<'a, 'b, K> Sub<&'b OrdSet<K>> for &'a OrdSet<K>
where
    K: Ord + Clone,
{
    type Output = OrdSet<K>;

    /// Returns the difference of `self` and `rhs` as a new `OrdSet<K>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    ///
    /// let a: OrdSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: OrdSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set = &a - &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn sub(self, rhs: &OrdSet<K>) -> OrdSet<K> {
        self.difference(rhs).cloned().collect()
    }
}

/// OrdSet iterator
pub struct Iter<'a, K: 'a> {
    iter: Keys<'a, K, ()>,
}

/// OrdSet move iterator
pub struct IntoIter<K> {
    iter: super::map::IntoIter<K, ()>,
}

/// Difference iterator
pub struct Difference<'a, K: 'a> {
    // iterator of the first set
    iter: Iter<'a, K>,
    // the second set
    other: &'a OrdSet<K>,
}

/// Set union iterator.
pub struct Union<'a, K: 'a> {
    iter: Chain<Iter<'a, K>, Difference<'a, K>>,
}

impl<K: Ord> IntoIterator for OrdSet<K> {
    type Item = K;
    type IntoIter = IntoIter<K>;

    /// Creates a consuming iterator, that is, one that moves each value out
    /// of the set in arbitrary order. The set cannot be used after calling
    /// this.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdSet;
    /// let mut set = OrdSet::new();
    /// set.insert("a".to_string());
    /// set.insert("b".to_string());
    ///
    /// // Not possible to collect to a Vec<String> with a regular `.iter()`.
    /// let v: Vec<String> = set.into_iter().collect();
    ///
    /// // Will print in an arbitrary order.
    /// for x in &v {
    ///     println!("{}", x);
    /// }
    /// ```
    fn into_iter(self) -> IntoIter<K> {
        IntoIter {
            iter: self.map.into_iter(),
        }
    }
}

impl<'a, K: Ord> IntoIterator for &'a OrdSet<K> {
    type Item = &'a K;
    type IntoIter = Iter<'a, K>;

    fn into_iter(self) -> Iter<'a, K> {
        self.iter()
    }
}

impl<'a, K> Clone for Iter<'a, K> {
    fn clone(&self) -> Iter<'a, K> {
        Iter {
            iter: self.iter.clone(),
        }
    }
}

macro_rules! impl_iter {
    ($typ:ty, $item:ty, $map:expr) => {
        impl<'a, K> Iterator for $typ {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next().map($map)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<'a, K> DoubleEndedIterator for $typ {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.iter.next_back().map($map)
            }
        }

        impl<'a, K> ExactSizeIterator for $typ {
            fn len(&self) -> usize {
                self.iter.len()
            }
        }
    };
}

impl_iter!{ Iter<'a, K>, &'a K, |e| e }
impl_iter!{ IntoIter<K>, K, |(k, _)| k }

impl<'a, K> Clone for Difference<'a, K> {
    fn clone(&self) -> Difference<'a, K> {
        Difference {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, K: Ord> Iterator for Difference<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        loop {
            match self.iter.next() {
                None => return None,
                Some(elt) => if !self.other.contains(elt) {
                    return Some(elt);
                },
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<'a, K> Clone for Union<'a, K> {
    fn clone(&self) -> Union<'a, K> {
        Union {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, K: Ord> Iterator for Union<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[allow(dead_code)]
fn assert_covariance() {
    fn set<'new>(v: OrdSet<&'static str>) -> OrdSet<&'new str> {
        v
    }
    fn iter<'a, 'new>(v: Iter<'a, &'static str>) -> Iter<'a, &'new str> {
        v
    }
    fn into_iter<'new>(v: IntoIter<&'static str>) -> IntoIter<&'new str> {
        v
    }
    fn difference<'a, 'new>(v: Difference<'a, &'static str>) -> Difference<'a, &'new str> {
        v
    }
    fn union<'a, 'new>(v: Union<'a, &'static str>) -> Union<'a, &'new str> {
        v
    }
}
