//! Define the Meter trait to track cache resource usage.

use std::borrow::Borrow;

/// A trait for measuring the size of a cache item.
///
/// `Meter` is used to provide the cache an additional method to track the resource usage, other
/// than counting cache items. This is useful when the cache items differ in size.
///
/// In most cases, using `usize` as `Measure` would be good enough.
pub trait Meter<K, V> {
    /// The type used to store measurements.
    type Measure: Default
        + Copy
        + Ord
        + std::fmt::Display
        + std::ops::Add<Output = Self::Measure>
        + std::ops::Sub<Output = Self::Measure>;

    /// Calculate the size of `key` and `value`.
    fn measure<Q: ?Sized>(&self, key: &Q, value: &V) -> Self::Measure
    where
        K: Borrow<Q>;
}

/// A Meter that measures cache size by counting object number.
pub struct Count;

impl<K, V> Meter<K, V> for Count {
    type Measure = usize;

    fn measure<Q: ?Sized>(&self, _: &Q, _: &V) -> Self::Measure
    where
        K: Borrow<Q>,
    {
        1
    }
}
