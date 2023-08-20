/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order.
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
/// for (k, v) in cache {
///     assert_eq!(k, n);
///     assert_eq!(v, n * 10);
///     n += 1;
/// }
///
/// assert_eq!(n, 4);
/// ```
#[derive(Clone)]
pub struct IntoIter<K, V>(pub(crate) linked_hash_map::IntoIter<K, V>);

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        self.0.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order.
///
/// Accessing a cache through the iterator does _not_ affect the cache's LRU
/// state.
pub struct Iter<'a, K, V>(pub(crate) linked_hash_map::Iter<'a, K, V>);

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        Iter(self.0.clone())
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        self.0.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order with mutable references to the values.
///
/// Accessing a cache through the iterator does _not_ affect the cache's LRU
/// state.
pub struct IterMut<'a, K, V>(pub(crate) linked_hash_map::IterMut<'a, K, V>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.0.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
