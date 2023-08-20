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
//! # use lru_cache::LruCache;
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
//! key-value pairs, see [`LruCache::with_meter`] for more
//! information. If the `heapsize` feature is enabled, this crate provides one
//! such alternate metric&mdash;`HeapSize`. Custom metrics can be written by
//! implementing the [`Meter`] trait.

#[cfg(feature = "heapsize")]
extern crate heapsize;

use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt;
use std::hash::BuildHasher;
use std::hash::Hash;

use cache_iter::IntoIter;
use cache_iter::Iter;
use cache_iter::IterMut;
use linked_hash_map::LinkedHashMap;

mod cache_iter;
pub mod meter;

// FIXME(conventions): implement indexing?

#[cfg(feature = "heapsize")]
mod heap_meter {
    use std::borrow::Borrow;

    use heapsize::HeapSizeOf;

    /// Size limit based on the heap size of each cache item.
    ///
    /// Requires cache items that implement [`HeapSizeOf`][1].
    ///
    /// [1]: https://doc.servo.org/heapsize/trait.HeapSizeOf.html
    pub struct HeapSize;

    impl<K, V: HeapSizeOf> super::Meter<K, V> for HeapSize {
        type Measure = usize;

        fn measure<Q: ?Sized>(&self, _: &Q, item: &V) -> usize
        where
            K: Borrow<Q>,
        {
            item.heap_size_of_children() + ::std::mem::size_of::<V>()
        }
    }
}

#[cfg(feature = "heapsize")]
pub use heap_meter::*;
use meter::Count;

use crate::meter::Meter;

/// An LRU cache.
#[derive(Clone)]
pub struct LruCache<K: Eq + Hash, V, S: BuildHasher = RandomState, M: Meter<K, V> = Count> {
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
    /// # use lru_cache::LruCache;
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

impl<K: Eq + Hash, V, M: Meter<K, V>> LruCache<K, V, RandomState, M> {
    /// Creates an empty cache that can hold at most `capacity` as measured by
    /// [`Meter`].
    ///
    /// You can implement the [`Meter`] trait to allow custom metrics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::{LruCache, meter::Meter};
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
    ) -> LruCache<K, V, RandomState, M> {
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
    /// Returns a mutable reference to the value corresponding to the given key
    /// in the cache, if any.
    ///
    /// Note that this method is not available for cache objects using `Meter`
    /// implementations other than `Count`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(2, "c");
    /// cache.insert(3, "d");
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "c"));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get_refresh(k)
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
    /// # use lru_cache::LruCache;
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
    /// assert_eq!(cache.get_mut(&2), Some(&mut 200));
    /// assert_eq!(cache.get_mut(&3), Some(&mut 300));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.internal_iter_mut()
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

    /// Returns the maximum size of the key-value pairs the cache can hold, as
    /// measured by the [`Meter`] used by the cache.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
    /// let mut cache: LruCache<i32, &str> = LruCache::new(2);
    /// assert_eq!(cache.capacity(), 2);
    /// ```
    pub fn capacity(&self) -> M::Measure {
        self.max_capacity
    }

    pub fn max_items(&self) -> usize {
        self.max_items
    }

    /// Checks if the map contains the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
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

    pub fn get<Q: ?Sized>(&mut self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get_refresh(k).map(|v| v as &V)
    }

    /// Inserts a key-value pair into the cache. If the key already existed, the
    /// old value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// assert_eq!(cache.get_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let new_size = self.meter.measure(&k, &v);
        self.current_measure = self.current_measure + new_size;

        if let Some(old) = self.map.get(&k) {
            self.current_measure = self.current_measure - self.meter.measure(&k, old);
        }

        let old_val = self.map.insert(k, v);

        // Evict items until we're below both count capacity and size capacity.

        while self.len() > self.max_items() {
            self.remove_lru();
        }

        while self.size() > self.capacity() {
            self.remove_lru();
        }
        old_val
    }

    /// Removes the given key from the cache and returns its corresponding
    /// value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
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
            self.current_measure = self.current_measure - self.meter.measure(k, &v);
            v
        })
    }

    /// Sets the max number of items the cache can hold.
    ///
    /// Removes least-recently-used key-value pairs if necessary.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    /// cache.set_capacity(100);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_max_items(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_max_items(1);
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), None);
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    /// ```
    pub fn set_max_items(&mut self, max_items: usize) {
        while self.len() > max_items {
            self.remove_lru();
        }
        self.max_items = max_items;
    }

    /// Sets the size of the key-value pairs the cache can hold, as measured by
    /// the [`Meter`] used by the cache.
    ///
    /// Removes least-recently-used key-value pairs if necessary.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
    /// #
    /// let mut cache = LruCache::new(2);
    /// cache.set_max_items(100);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_capacity(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_capacity(1);
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), None);
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    /// ```
    pub fn set_capacity(&mut self, capacity: M::Measure) {
        while self.size() > capacity {
            self.remove_lru();
        }
        self.max_capacity = capacity;
    }

    /// Removes and returns the least recently used key-value pair as a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use lru_cache::LruCache;
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
            self.current_measure = self.current_measure - self.meter.measure(&k, &v);
            (k, v)
        })
    }

    /// Returns the number of key-value pairs in the cache.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the size in `Meter::Measure` of all the key-value pairs in the cache.
    pub fn size(&self) -> M::Measure {
        self.current_measure
    }

    /// Returns `true` if the cache contains no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
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
    /// # use lru_cache::LruCache;
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

    fn internal_iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut(self.map.iter_mut())
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

    use super::LruCache;
    use crate::meter::Meter;

    #[test]
    fn test_put_and_get() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        assert_eq!(cache.get_mut(&1), Some(&mut 10));
        assert_eq!(cache.get_mut(&2), Some(&mut 20));
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.size(), 2);
    }

    #[test]
    fn test_put_update() {
        let mut cache = LruCache::new(1);
        cache.insert("1", 10);
        cache.insert("1", 19);
        assert_eq!(cache.get_mut("1"), Some(&mut 19));
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
        assert_eq!(cache.get_mut(&6), Some(&mut 60));
        assert_eq!(cache.get_mut(&7), Some(&mut 70));
        assert_eq!(cache.get_mut(&8), Some(&mut 80));
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

    #[cfg(feature = "heapsize")]
    #[test]
    fn test_heapsize_cache() {
        use super::HeapSize;

        let mut cache = LruCache::<&str, (u8, u8, u8), _, _>::with_meter(8, HeapSize);
        cache.insert("foo1", (1, 2, 3));
        cache.insert("foo2", (4, 5, 6));
        cache.insert("foo3", (7, 8, 9));
        assert!(!cache.contains_key("foo1"));
        cache.insert("foo2", (10, 11, 12));
        cache.insert("foo4", (13, 14, 15));
        assert!(!cache.contains_key("foo3"));
    }
}
