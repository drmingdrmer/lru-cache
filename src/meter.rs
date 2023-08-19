//! Define the Meter trait to track cache resource usage.

use std::borrow::Borrow;

/// A trait for measuring the size of a cache entry.
///
/// If you implement this trait, you should use `usize` as the `Measure` type,
/// otherwise you will also have to implement [`Countable`] for your Meter type.
pub trait Meter<K, V> {
    /// The type used to store measurements.
    type Measure: Default + Copy;

    /// Calculate the size of `key` and `value`.
    fn measure<Q: ?Sized>(&self, key: &Q, value: &V) -> Self::Measure
    where
        K: Borrow<Q>;
}

/// CountableMeter tracks the resource used in the cache.
pub trait CountableMeter<K, V>: Meter<K, V> + Countable<K, V, Self::Measure> {}

/// `Count` is all no-ops, the number of entries in the map is the size.
impl<K, V, T> CountableMeter<K, V> for T
where
    T: Meter<K, V>,
    T: Countable<K, V, <T as Meter<K, V>>::Measure>,
{
}

/// Define how to cumulatively add and subtract measurements.
pub trait Countable<K, V, M> {
    /// Add `amount` to `current` and return the sum.
    fn add(&self, current: M, amount: M) -> M;

    /// Subtract `amount` from `current` and return the difference.
    fn sub(&self, current: M, amount: M) -> M;

    /// Return `current` as a `usize` if possible, otherwise return `None`.
    ///
    /// If this method returns `None` the cache will use the number of cache
    /// entries as its size.
    fn size(&self, current: M) -> Option<u64>;
}

/// For any other `Meter` with `Measure=usize`, just do the simple math.
impl<K, V, T> Countable<K, V, usize> for T
where
    T: Meter<K, V>,
{
    fn add(&self, current: usize, amount: usize) -> usize {
        current + amount
    }
    fn sub(&self, current: usize, amount: usize) -> usize {
        current - amount
    }
    fn size(&self, current: usize) -> Option<u64> {
        Some(current as u64)
    }
}
