// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A cache that holds a limited number of key-value pairs. When the
//! capacity of the cache is exceeded, the least-recently-used
//! (where "used" means a look-up or putting the pair into the cache)
//! pair is automatically removed.
//!
//! # Examples
//!
//! ```rust
//! # use lru_cache_map::LruCache;
//! #
//! let mut cache = LruCache::new(2);
//!
//! cache.insert(1, 10);
//! cache.insert(2, 20);
//! cache.insert(3, 30);
//! assert!(cache.get_mut(&1).is_none());
//! assert_eq!(*cache.get_mut(&2).unwrap(), 20);
//! assert_eq!(*cache.get_mut(&3).unwrap(), 30);
//!
//! cache.insert(2, 22);
//! assert_eq!(*cache.get_mut(&2).unwrap(), 22);
//!
//! cache.insert(6, 60);
//! assert!(cache.get_mut(&3).is_none());
//!
//! cache.set_capacity(1);
//! assert!(cache.get_mut(&2).is_none());
//! ```
//!
//! The cache can also be limited by an arbitrary metric calculated from its
//! key-value pairs, see [`LruCache::with_meter`] for more information. Custom metrics can be
//! written by implementing the [`Meter`] trait.

use std::borrow::Borrow;
use std::fmt;
use std::hash::BuildHasher;
use std::hash::Hash;

pub use hashbrown;
use hashbrown::hash_map::DefaultHashBuilder;
use hashlink::linked_hash_map;
use hashlink::linked_hash_map::RawEntryMut;
use linked_hash_map::LinkedHashMap;

use crate::cache_iter::IntoIter;
use crate::cache_iter::Iter;
use crate::cache_iter::IterMut;
use crate::meter::Count;
use crate::meter::Meter;
use crate::peek_mut::PeekMut;

mod cache_iter;
pub mod meter;
mod peek_mut;

/// An LRU cache.
#[derive(Clone)]
pub struct LruCache<K: Eq + Hash, V, S: BuildHasher = DefaultHashBuilder, M: Meter<K, V> = Count> {
    map: LinkedHashMap<K, V, S>,

    /// The maximum number of items this cache can hold.
    max_items: usize,

    meter: M,
    current_measure: M::Measure,
    max_capacity: M::Measure,
}

impl<K: Eq + Hash, V> LruCache<K, V> {
    /// Creates an empty cache that can hold at most `max_items` items.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// let mut cache: LruCache<i32, &str> = LruCache::new(10);
    /// ```
    pub fn new(max_items: usize) -> Self {
        LruCache {
            map: LinkedHashMap::new(),
            // By default Meter is `Count` so that max_item is the same as capacity;
            max_items,
            current_measure: 0,
            max_capacity: max_items,
            meter: Count,
        }
    }
}

impl<K: Eq + Hash, V, M: Meter<K, V>> LruCache<K, V, DefaultHashBuilder, M> {
    /// Creates an empty cache that can hold at most `capacity` as measured by
    /// [`Meter`].
    ///
    /// You can implement the [`Meter`] trait to allow custom metrics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::{LruCache, meter::Meter};
    /// # use std::borrow::Borrow;
    /// #
    /// /// Measure Vec items by their length
    /// struct VecLen;
    ///
    /// impl<K, T> Meter<K, Vec<T>> for VecLen {
    ///     type Measure = usize;
    ///     fn measure<Q: ?Sized>(&self, _: &Q, v: &Vec<T>) -> usize
    ///         where K: Borrow<Q>
    ///     {
    ///         v.len()
    ///     }
    /// }
    ///
    /// let mut cache = LruCache::with_meter(100, 5, VecLen);
    ///
    /// cache.insert(1, vec![1, 2]);
    /// assert_eq!(cache.size(), 2);
    ///
    /// cache.insert(2, vec![3, 4]);
    /// cache.insert(3, vec![5, 6]);
    /// assert_eq!(cache.size(), 4);
    /// assert_eq!(cache.len(), 2);
    /// ```
    pub fn with_meter(
        max_items: usize,
        capacity: M::Measure,
        meter: M,
    ) -> LruCache<K, V, DefaultHashBuilder, M> {
        LruCache {
            map: LinkedHashMap::new(),
            max_items,
            current_measure: Default::default(),
            max_capacity: capacity,
            meter,
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> LruCache<K, V, S, Count> {
    /// Creates an empty cache that can hold at most `capacity` items with the
    /// given hash builder.
    pub fn with_hasher(capacity: usize, hash_builder: S) -> LruCache<K, V, S, Count> {
        LruCache {
            map: LinkedHashMap::with_hasher(hash_builder),
            max_items: capacity,
            current_measure: 0,
            max_capacity: capacity,
            meter: Count,
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher, M: Meter<K, V>> LruCache<K, V, S, M> {
    /// Creates an empty cache that can hold at most `capacity` as measured by
    /// [`Meter`] with the given hash builder.
    pub fn with_meter_and_hasher(
        max_items: usize,
        capacity: M::Measure,
        meter: M,
        hash_builder: S,
    ) -> Self {
        LruCache {
            map: LinkedHashMap::with_hasher(hash_builder),
            max_items,
            current_measure: Default::default(),
            max_capacity: capacity,
            meter,
        }
    }

    /// Returns `true` if the cache contains no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of key-value pairs in the cache.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn max_items(&self) -> usize {
        self.max_items
    }

    /// Sets the max number of items the cache can hold.
    ///
    /// Removes least-recently-used key-value pairs if necessary.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    /// cache.set_capacity(100);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_max_items(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_max_items(1);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), None);
    /// assert_eq!(cache.get(&3), Some(&"c"));
    /// ```
    pub fn set_max_items(&mut self, max_items: usize) {
        self.max_items = max_items;
        self.evict_by_policy();
    }

    /// Returns the size in `Meter::Measure` of all the key-value pairs in the cache.
    pub fn size(&self) -> M::Measure {
        self.current_measure
    }

    /// Returns the maximum size of the key-value pairs the cache can hold, as
    /// measured by the [`Meter`] used by the cache.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// let mut cache: LruCache<i32, &str> = LruCache::new(2);
    /// assert_eq!(cache.capacity(), 2);
    /// ```
    pub fn capacity(&self) -> M::Measure {
        self.max_capacity
    }

    /// Sets the size of the key-value pairs the cache can hold, as measured by
    /// the [`Meter`] used by the cache.
    ///
    /// Removes least-recently-used key-value pairs if necessary.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    /// cache.set_max_items(100);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(1);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), None);
    /// assert_eq!(cache.get(&3), Some(&"c"));
    /// ```
    pub fn set_capacity(&mut self, capacity: M::Measure) {
        self.max_capacity = capacity;
        self.evict_by_policy();
    }

    /// Checks if the map contains the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(1);
    ///
    /// cache.insert(1, "a");
    /// assert!(cache.contains_key(&1));
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the given key
    /// in the cache, if any. **Do not** put the accessed item to the back.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(2, "c");
    /// cache.insert(3, "d");
    ///
    /// assert_eq!(cache.peek(&1), None);
    /// assert_eq!(cache.peek(&2), Some(&"c"));
    /// ```
    pub fn peek<Q: ?Sized>(&mut self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.map.raw_entry_mut().from_key(k) {
            RawEntryMut::Occupied(occupied) => Some(occupied.into_mut()),
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the given key
    /// in the cache, if any. **Do** put the accessed item to the back.
    ///
    /// When the mutable reference is dropped, the cache will be evicted by policy if the `measure`
    /// of the updated value changes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// # use std::ops::DerefMut;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// {
    ///     let mut a = cache.peek_mut(&1).unwrap();
    ///     *a = "c";
    /// }
    ///
    /// assert_eq!(cache.get(&1).unwrap(), &"c");
    /// assert_eq!(cache.get(&2).unwrap(), &"b");
    /// ```
    pub fn peek_mut<'a, Q: ?Sized>(&'a mut self, k: &'a Q) -> Option<PeekMut<'a, K, V, S, M>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let me = self as *mut Self;

        match self.map.raw_entry_mut().from_key(k) {
            RawEntryMut::Occupied(occupied) => {
                let p = PeekMut::new(occupied, me);
                Some(p)
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Returns a reference to the value corresponding to the given key
    /// in the cache, if any. And put the accessed item to the back.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(2, "c");
    /// cache.insert(3, "d");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// ```
    pub fn get<Q: ?Sized>(&mut self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.map.raw_entry_mut().from_key(k) {
            RawEntryMut::Occupied(mut occupied) => {
                occupied.to_back();
                Some(occupied.into_mut())
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the given key
    /// in the cache, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// # use std::ops::DerefMut;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// {
    ///     let mut a = cache.get_mut(&1).unwrap();
    ///     *a = "c";
    /// }
    ///
    /// assert_eq!(cache.get(&1).unwrap(), &"c");
    /// assert_eq!(cache.get(&2).unwrap(), &"b");
    /// ```
    pub fn get_mut<'a, Q: ?Sized>(&'a mut self, k: &'a Q) -> Option<PeekMut<'a, K, V, S, M>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let me = self as *mut Self;

        match self.map.raw_entry_mut().from_key(k) {
            RawEntryMut::Occupied(mut occupied) => {
                occupied.to_back();
                let p = PeekMut::new(occupied, me);
                Some(p)
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Inserts a key-value pair into the cache and put it to the back. If the key already existed,
    /// the old value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    ///
    /// let evicted = cache.insert(2, "c");
    /// assert_eq!(evicted, Some("b"));
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.measure_add(&k, &v);

        let old_val = match self.map.raw_entry_mut().from_key(&k) {
            RawEntryMut::Occupied(mut occupied) => {
                occupied.to_back();
                let old_val = occupied.replace_value(v);

                self.measure_remove(&k, &old_val);
                Some(old_val)
            }
            RawEntryMut::Vacant(vacant) => {
                vacant.insert(k, v);
                None
            }
        };

        self.evict_by_policy();

        old_val
    }

    /// Removes the given key from the cache and returns its corresponding
    /// value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(2, "a");
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.remove(k).map(|v| {
            self.measure_remove(k, &v);
            v
        })
    }

    /// Removes and returns the least recently used key-value pair as a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.remove_lru(), Some((1, "a")));
    /// assert_eq!(cache.len(), 1);
    /// ```
    #[inline]
    pub fn remove_lru(&mut self) -> Option<(K, V)> {
        self.map.pop_front().map(|(k, v)| {
            self.measure_remove(&k, &v);
            (k, v)
        })
    }

    /// Removes all key-value pairs from the cache.
    pub fn clear(&mut self) {
        self.map.clear();
        self.current_measure = Default::default();
    }

    /// Returns an iterator over the cache's key-value pairs in least- to
    /// most-recently-used order.
    ///
    /// Accessing the cache through the iterator does _not_ affect the cache's
    /// LRU state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, 10);
    /// cache.insert(2, 20);
    /// cache.insert(3, 30);
    ///
    /// let kvs: Vec<_> = cache.iter().collect();
    /// assert_eq!(kvs, [(&2, &20), (&3, &30)]);
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter(self.map.iter())
    }

    /// Returns an iterator over the cache's key-value pairs in least- to
    /// most-recently-used order, with mutable references to the values.
    ///
    /// Accessing the cache through the iterator does _not_ affect the cache's
    /// LRU state. Note that this method is not available for cache objects
    /// using `Meter` implementations. other than `Count`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache_map::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, 10);
    /// cache.insert(2, 20);
    /// cache.insert(3, 30);
    ///
    /// let mut n = 2;
    ///
    /// for (k, v) in cache.iter_mut() {
    ///     assert_eq!(*k, n);
    ///     assert_eq!(*v, n * 10);
    ///     *v *= 10;
    ///     n += 1;
    /// }
    ///
    /// assert_eq!(n, 4);
    /// assert_eq!(cache.get(&2), Some(&200));
    /// assert_eq!(cache.get(&3), Some(&300));
    /// ```
    // TODO: validate against `Meter` when the updated value is given back
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.internal_iter_mut()
    }

    fn internal_iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut(self.map.iter_mut())
    }

    /// Evict least recent used items until both count and size are below their limit.
    pub(crate) fn evict_by_policy(&mut self) {
        while self.len() > self.max_items() {
            self.remove_lru();
        }
        while self.size() > self.capacity() {
            self.remove_lru();
        }
    }

    pub(crate) fn measure_add<Q: ?Sized>(&mut self, k: &Q, v: &V) -> M::Measure
    where
        K: Borrow<Q>,
    {
        self.current_measure = self.current_measure + self.meter.measure(k, v);
        self.current_measure
    }

    pub(crate) fn measure_remove<Q: ?Sized>(&mut self, k: &Q, v: &V) -> M::Measure
    where
        K: Borrow<Q>,
    {
        self.current_measure = self.current_measure - self.meter.measure(k, v);
        self.current_measure
    }
}

impl<K: Eq + Hash, V, S: BuildHasher, M: Meter<K, V>> Extend<(K, V)> for LruCache<K, V, S, M> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: fmt::Debug + Eq + Hash, V: fmt::Debug, S: BuildHasher, M: Meter<K, V>> fmt::Debug
    for LruCache<K, V, S, M>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter().rev()).finish()
    }
}

impl<K: Eq + Hash, V, S: BuildHasher, M: Meter<K, V>> IntoIterator for LruCache<K, V, S, M> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter(self.map.into_iter())
    }
}

impl<'a, K: Eq + Hash, V, S: BuildHasher, M: Meter<K, V>> IntoIterator
    for &'a LruCache<K, V, S, M>
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Eq + Hash, V, S: BuildHasher, M: Meter<K, V>> IntoIterator
    for &'a mut LruCache<K, V, S, M>
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.internal_iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Borrow;
    use std::ops::Deref;

    use super::LruCache;
    use crate::meter::Meter;

    #[test]
    fn test_put_and_get() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        assert_eq!(cache.get_mut(&1).unwrap().deref(), &mut 10);
        assert_eq!(cache.get_mut(&2).unwrap().deref(), &mut 20);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.size(), 2);
    }

    #[test]
    fn test_put_update() {
        let mut cache = LruCache::new(1);
        cache.insert("1", 10);
        cache.insert("1", 19);
        assert_eq!(cache.get_mut("1").unwrap().deref(), &mut 19);
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_contains_key() {
        let mut cache = LruCache::new(1);
        cache.insert("1", 10);
        assert!(cache.contains_key("1"));
    }

    #[test]
    fn test_expire_lru() {
        let mut cache = LruCache::new(2);
        cache.insert("foo1", "bar1");
        cache.insert("foo2", "bar2");
        cache.insert("foo3", "bar3");
        assert!(cache.get_mut("foo1").is_none());
        cache.insert("foo2", "bar2update");
        cache.insert("foo4", "bar4");
        assert!(cache.get_mut("foo3").is_none());
    }

    #[test]
    fn test_pop() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        assert_eq!(cache.len(), 2);
        let opt1 = cache.remove(&1);
        assert!(opt1.is_some());
        assert_eq!(opt1.unwrap(), 10);
        assert!(cache.get_mut(&1).is_none());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_change_capacity() {
        let mut cache = LruCache::new(2);
        assert_eq!(cache.capacity(), 2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.set_capacity(1);
        assert!(cache.get_mut(&1).is_none());
        assert_eq!(cache.capacity(), 1);
    }

    #[test]
    fn test_debug() {
        let mut cache = LruCache::new(3);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        assert_eq!(format!("{:?}", cache), "{3: 30, 2: 20, 1: 10}");
        cache.insert(2, 22);
        assert_eq!(format!("{:?}", cache), "{2: 22, 3: 30, 1: 10}");
        cache.insert(6, 60);
        assert_eq!(format!("{:?}", cache), "{6: 60, 2: 22, 3: 30}");
        cache.get_mut(&3);
        assert_eq!(format!("{:?}", cache), "{3: 30, 6: 60, 2: 22}");
        cache.set_capacity(2);
        assert_eq!(format!("{:?}", cache), "{3: 30, 6: 60}");
    }

    #[test]
    fn test_remove() {
        let mut cache = LruCache::new(3);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        cache.insert(4, 40);
        cache.insert(5, 50);
        cache.remove(&3);
        cache.remove(&4);
        assert!(cache.get_mut(&3).is_none());
        assert!(cache.get_mut(&4).is_none());
        cache.insert(6, 60);
        cache.insert(7, 70);
        cache.insert(8, 80);
        assert!(cache.get_mut(&5).is_none());
        assert_eq!(cache.get_mut(&6).unwrap().deref(), &mut 60);
        assert_eq!(cache.get_mut(&7).unwrap().deref(), &mut 70);
        assert_eq!(cache.get_mut(&8).unwrap().deref(), &mut 80);
    }

    #[test]
    fn test_get_mut_debug() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        let a = cache.get_mut(&1).unwrap();

        assert_eq!("PeekMut(10)", format!("{:?}", a))
    }

    #[test]
    fn test_get_mut_evict() {
        // When a value is updated via `get_mut()` and given back to the cache,
        // the cache should evict items according to the meter changes.

        let mut cache = LruCache::with_meter(2, 5, VecLen);
        cache.insert(1, b"12".to_vec());
        cache.insert(2, b"34".to_vec());

        assert_eq!(cache.len(), 2);

        {
            let mut a = cache.get_mut(&1).unwrap();
            *a = b"1234".to_vec();
        }

        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&1).unwrap(), &b"1234".to_vec());

        {
            let mut a = cache.get_mut(&1).unwrap();
            *a = b"123456".to_vec();
        }

        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_peek() {
        let mut cache = LruCache::with_meter(2, 5, VecLen);
        cache.insert(1, b"12".to_vec());
        cache.insert(2, b"34".to_vec());

        // peek() does not update the recency of `1`.
        assert_eq!(cache.peek(&1).unwrap(), &b"12".to_vec());

        // still evict `1`, because peek() does not update its recency
        cache.insert(3, b"33".to_vec());
        assert_eq!(cache.peek(&1), None);
    }

    #[test]
    fn test_peek_mut() {
        let mut cache = LruCache::with_meter(2, 5, VecLen);
        cache.insert(1, b"12".to_vec());
        cache.insert(2, b"34".to_vec());

        {
            let mut a = cache.peek_mut(&1).unwrap();
            *a = b"56".to_vec();
        }
        // `1` is updated
        assert_eq!(cache.peek(&1).unwrap(), &b"56".to_vec());

        // still evict `1`, because peek() does not update its recency
        cache.insert(3, b"33".to_vec());
        assert_eq!(cache.peek(&1), None);
    }

    #[test]
    fn test_peek_mut_evict() {
        // When a value is updated via `peek_mut()` and given back to the cache,
        // the cache should evict items according to the meter changes.

        let mut cache = LruCache::with_meter(2, 5, VecLen);
        cache.insert(1, b"12".to_vec());
        cache.insert(2, b"34".to_vec());

        assert_eq!(cache.len(), 2);

        {
            let mut a = cache.peek_mut(&1).unwrap();
            *a = b"1234".to_vec();
        }

        assert_eq!(cache.len(), 1);
        // Because peek does not update the recency, `1` is evicted
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2).unwrap(), &b"34".to_vec());
    }

    #[test]
    fn test_clear() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.clear();

        assert!(cache.get_mut(&1).is_none());
        assert!(cache.get_mut(&2).is_none());
        assert_eq!(format!("{:?}", cache), "{}");
    }

    #[test]
    fn test_iter() {
        let mut cache = LruCache::new(3);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        cache.insert(4, 40);
        cache.insert(5, 50);
        assert_eq!(cache.iter().collect::<Vec<_>>(), [
            (&3, &30),
            (&4, &40),
            (&5, &50)
        ]);
        assert_eq!(cache.iter_mut().collect::<Vec<_>>(), [
            (&3, &mut 30),
            (&4, &mut 40),
            (&5, &mut 50)
        ]);
        assert_eq!(cache.iter().rev().collect::<Vec<_>>(), [
            (&5, &50),
            (&4, &40),
            (&3, &30)
        ]);
        assert_eq!(cache.iter_mut().rev().collect::<Vec<_>>(), [
            (&5, &mut 50),
            (&4, &mut 40),
            (&3, &mut 30)
        ]);
    }

    struct VecLen;

    impl<K, T> Meter<K, Vec<T>> for VecLen {
        type Measure = usize;
        fn measure<Q: ?Sized>(&self, _: &Q, v: &Vec<T>) -> usize
        where
            K: Borrow<Q>,
        {
            v.len()
        }
    }

    #[test]
    fn test_metered_cache() {
        let mut cache = LruCache::with_meter(100, 5, VecLen);
        cache.insert("foo1", vec![1, 2]);
        assert_eq!(cache.size(), 2);
        cache.insert("foo2", vec![3, 4]);
        cache.insert("foo3", vec![5, 6]);
        assert_eq!(cache.size(), 4);
        assert!(!cache.contains_key("foo1"));
        cache.insert("foo2", vec![7, 8]);
        cache.insert("foo4", vec![9, 10]);
        assert_eq!(cache.size(), 4);
        assert!(!cache.contains_key("foo3"));
        assert_eq!(cache.get("foo2"), Some(&vec![7, 8]));
    }

    #[test]
    fn test_metered_cache_reinsert_larger_capacity() {
        let mut cache = LruCache::with_meter(100, 5, VecLen);
        cache.insert("foo1", vec![1, 2]);
        cache.insert("foo2", vec![3, 4]);
        assert_eq!(cache.size(), 4);
        cache.insert("foo2", vec![5, 6, 7, 8]);
        assert_eq!(cache.size(), 4);
        assert!(!cache.contains_key("foo1"));
    }

    #[test]
    fn test_metered_cache_reinsert_larger_max_items() {
        let mut cache = LruCache::with_meter(2, 100, VecLen);

        cache.insert("foo1", vec![1, 2]);
        cache.insert("foo2", vec![3, 4]);
        assert_eq!(cache.len(), 2);

        cache.insert("foo2", vec![5, 6, 7, 8]);
        assert_eq!(cache.len(), 2);
        assert!(cache.contains_key("foo1"));

        cache.insert("foo3", vec![9, 10]);
        assert_eq!(cache.len(), 2);
        assert!(!cache.contains_key("foo1"));
    }

    #[test]
    fn test_metered_cache_oversize() {
        let mut cache = LruCache::with_meter(100, 2, VecLen);
        cache.insert("foo1", vec![1, 2]);
        cache.insert("foo2", vec![3, 4, 5, 6]);
        assert_eq!(cache.size(), 0);
        assert!(!cache.contains_key("foo1"));
        assert!(!cache.contains_key("foo2"));
    }

    #[test]
    fn test_metered_cache_over_max_items() {
        let mut cache = LruCache::with_meter(1, 100, VecLen);
        cache.insert("foo1", vec![1, 2]);
        cache.insert("foo2", vec![3, 4, 5, 6]);
        assert_eq!(cache.len(), 1);
        assert!(!cache.contains_key("foo1"));
        assert!(cache.contains_key("foo2"));
    }
}
