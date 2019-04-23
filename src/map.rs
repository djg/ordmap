use std::{
    borrow::Borrow,
    fmt::{self, Debug},
    iter, mem,
    ops::{Index, IndexMut},
    slice, vec,
};

use self::Entry::{Occupied, Vacant};

pub struct OrdMap<K, V> {
    elements: Vec<(K, V)>,
}

impl<K: Ord, V> OrdMap<K, V> {
    /// Creates an empty map. This method does not allocate.
    pub fn new() -> Self {
        OrdMap {
            elements: Vec::new(),
        }
    }

    /// Create an empty map with the given initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        OrdMap {
            elements: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordmap::OrdMap;
    /// let map: OrdMap<i32, String> = OrdMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    /// Reserves capacity for at least `additional` more to be inserted in the
    /// map. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.elements.reserve(additional);
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns an iterator yielding references to the map's keys and their
    /// corresponding values in arbitrary order.
    ///
    /// The iterator's item type is `(&K, &V)`.
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.elements.iter(),
        }
    }

    /// Returns an iterator yielding references to the map's keys and mutable
    /// references to their corresponding values in arbitrary order.
    ///
    /// The iterator's item type is `(&K, &mut V)`.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.elements.iter_mut(),
        }
    }

    /// Returns an iterator yielding references to the map's keys in arbitrary
    /// order.
    ///
    /// The iterator's item type is `&K`.
    pub fn keys(&self) -> Keys<K, V> {
        Keys { iter: self.iter() }
    }

    /// Returns an iterator yielding references to the map's values in arbitrary
    /// order.
    ///
    /// The iterator's item type is `&V`.
    pub fn values(&self) -> Values<K, V> {
        Values { iter: self.iter() }
    }

    /// Returns a reference to the value in the map whose key is equal to the
    /// given key.
    ///
    /// Returns `None` if the map contains no such key.
    ///
    /// The given key may be any borrowed form of the map's key type, but `Eq`
    /// on the borrowed form *must* match that of the key type.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        match self
            .elements
            .binary_search_by(|(k, _)| k.borrow().cmp(&key))
        {
            Ok(index) => Some(&self.elements[index].1),
            Err(_) => None,
        }
    }

    /// Returns a mutable reference to the value in the map whose key is equal
    /// to the given key.
    ///
    /// Returns `None` if the map contains no such key.
    ///
    /// The given key may be any borrowed form of the map's key type, but `Eq`
    /// on the borrowed form *must* match that of the key type.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        match self
            .elements
            .binary_search_by(|(k, _)| k.borrow().cmp(&key))
        {
            Ok(index) => Some(&mut self.elements[index].1),
            Err(_) => None,
        }
    }

    /// Checks if the map contains a key that is equal to the given key.
    ///
    /// The given key may be any borrowed form of the map's key type, but `Eq`
    /// on the borrowed form *must* match that of the key type.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.get(key).is_some()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// Returns `None` if the map did not contain a key that is equal to the
    /// given key.
    ///
    /// If the map did contain such a key, its corresponding value is replaced
    /// with the given value, and the old value is returned. The key is not
    /// updated, though. This matters for values that can be `==` without being
    /// identical. See the [standard library's documentation] [std] for more
    /// details.
    ///
    /// [std]: https://doc.rust-lang.org/nightly/std/collections/index.html#insert-and-complex-keys
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.entry(key) {
            Occupied(mut e) => Some(e.insert(value)),
            Vacant(e) => {
                e.insert(value);
                None
            }
        }
    }

    /// Removes the key in the map that is equal to the given key and returns
    /// its corresponding value.
    ///
    /// Returns `None` if the map contained no such key.
    ///
    /// The given key may be any borrowed form of the map's key type, but `Ord`
    /// on the borrowed form *must* match that of the key type.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        match self
            .elements
            .binary_search_by(|(k, _)| k.borrow().cmp(&key))
        {
            Ok(index) => Some(self.elements.remove(index).1),
            Err(_) => None,
        }
    }

    /// Returns the given key's corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.elements.binary_search_by(|(k, _)| k.cmp(&key)) {
            Err(index) => Vacant(VacantEntry {
                map: self,
                key,
                index,
            }),
            Ok(index) => Occupied(OccupiedEntry { map: self, index }),
        }
    }
}

impl<K, V> Clone for OrdMap<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        OrdMap {
            elements: self.elements.clone(),
        }
    }

    fn clone_from(&mut self, other: &Self) {
        self.elements.clone_from(&other.elements);
    }
}

impl<K, V> Debug for OrdMap<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self).finish()
    }
}

impl<K: Ord, V> Default for OrdMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord, V> Extend<(K, V)> for OrdMap<K, V> {
    fn extend<I>(&mut self, key_values: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        for (key, value) in key_values {
            self.insert(key, value);
        }
    }
}

impl<K: Ord, V> iter::FromIterator<(K, V)> for OrdMap<K, V> {
    fn from_iter<I>(key_values: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut map = Self::new();
        map.extend(key_values);
        map
    }
}

impl<'a, K, V, Q> Index<&'a Q> for OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Output = V;

    fn index(&self, key: &'a Q) -> &Self::Output {
        self.get(key).expect("key not found")
    }
}

impl<'a, K, V, Q> IndexMut<&'a Q> for OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    fn index_mut(&mut self, key: &'a Q) -> &mut Self::Output {
        self.get_mut(key).expect("key not found")
    }
}

impl<K, V> PartialEq for OrdMap<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.elements == other.elements
    }
}

impl<K: Eq, V: Eq> Eq for OrdMap<K, V> {}

/// A view into a single occupied location in a `OrdMap`.
///
/// See [`OrdMap::entry`](struct.OrdMap.html#method.entry) for details.
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    map: &'a mut OrdMap<K, V>,
    index: usize,
}

/// A view into a single vacant location in a `OrdMap`.
///
/// See [`OrdMap::entry`](struct.OrdMap.html#method.entry) for details.
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    map: &'a mut OrdMap<K, V>,
    key: K,
    index: usize,
}

/// A view into a single entry in a `OrdMap`.
///
/// See [`OrdMap::entry`](struct.OrdMap.html#method.entry) for details.
pub enum Entry<'a, K: 'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),

    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures that the entry is occupied by inserting the given value if it is
    /// vacant.
    ///
    /// Returns a mutable reference to the entry's value.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures that the entry is occupied by inserting the the result of the
    /// given function if it is vacant.
    ///
    /// Returns a mutable reference to the entry's value.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Returns a reference to the entry's value.
    pub fn get(&self) -> &V {
        &self.map.elements[self.index].1
    }

    /// Returns a mutable reference to the entry's value.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.elements[self.index].1
    }

    /// Returns a mutable reference to the entry's value with the same lifetime as the map.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map.elements[self.index].1
    }

    /// Replaces the entry's value with the given one and returns the previous value.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Inserts the entry into the map with the given value.
    ///
    /// Returns a mutable reference to the entry's value with the same lifetime as the map.
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.elements.insert(self.index, (self.key, value));
        &mut self.map.elements[self.index].1
    }
}

/// A consuming iterator over an `OrdMap`.
pub struct IntoIter<K, V> {
    iter: vec::IntoIter<(K, V)>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        self.iter.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

/// An iterator yielding references to a `OrdMap`'s keys and their corresponding values.
///
/// See [`OrdMap::iter`](struct.OrdMap.html#method.iter) for details.
pub struct Iter<'a, K: 'a, V: 'a> {
    iter: slice::Iter<'a, (K, V)>,
}

/// An iterator yielding references to a `OrdMap`'s keys and mutable references to their
/// corresponding values.
///
/// See [`OrdMap::iter_mut`](struct.OrdMap.html#method.iter_mut) for details.
pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: slice::IterMut<'a, (K, V)>,
}

/// An iterator yielding references to a `OrdMap`'s keys in arbitrary order.
///
/// See [`OrdMap::keys`](struct.OrdMap.html#method.keys) for details.
pub struct Keys<'a, K: 'a, V: 'a> {
    iter: Iter<'a, K, V>,
}

/// An iterator yielding references to a `OrdMap`'s values in arbitrary order.
///
/// See [`OrdMap::values`](struct.OrdMap.html#method.values) for details.
pub struct Values<'a, K: 'a, V: 'a> {
    iter: Iter<'a, K, V>,
}

macro_rules! impl_iter {
    ($typ:ty, $item:ty, $map:expr) => {
        impl<'a, K, V> Iterator for $typ {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next().map($map)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<'a, K, V> DoubleEndedIterator for $typ {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.iter.next_back().map($map)
            }
        }

        impl<'a, K, V> ExactSizeIterator for $typ {
            fn len(&self) -> usize {
                self.iter.len()
            }
        }
    };
}

impl<K: Ord, V> IntoIterator for OrdMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            iter: self.elements.into_iter(),
        }
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a OrdMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a mut OrdMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl_iter!{Iter<'a,K,V>,  (&'a K, &'a V),  |e| (&e.0, &e.1) }
impl_iter!{IterMut<'a,K,V>,  (&'a K, &'a mut V),  |e| (&e.0, &mut e.1) }
impl_iter!{Keys<'a,K,V>,  &'a K,  |e| e.0 }
impl_iter!{Values<'a,K,V>, &'a V, |e| e.1 }

macro_rules! impl_clone {
    ($($typ:ident)+) => {
        $(impl<'a, K, V> Clone for $typ<'a, K, V> {
            fn clone(&self) -> Self {
                $typ {
                    iter: self.iter.clone(),
                }
            }
        })*
    };
}

impl_clone!{ Iter Keys Values }

#[allow(dead_code)]
fn assert_covariance() {
    fn map<'a, K, V>(x: OrdMap<&'static K, &'static V>) -> OrdMap<&'a K, &'a V> {
        x
    }
    fn iter<'i, 'a, K, V>(x: Iter<'i, &'static K, &'static V>) -> Iter<'i, &'a K, &'a V> {
        x
    }
    fn into_iter<'a, K, V>(x: IntoIter<&'static K, &'static V>) -> IntoIter<&'a K, &'a V> {
        x
    }
    fn keys<'i, 'a, K, V>(x: Keys<'i, &'static K, &'static V>) -> Keys<'i, &'a K, &'a V> {
        x
    }
    fn value<'i, 'a, K, V>(x: Values<'i, &'static K, &'static V>) -> Values<'i, &'a K, &'a V> {
        x
    }
}
