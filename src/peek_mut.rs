use std::fmt::Debug;
use std::fmt::Formatter;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::ops::Deref;
use std::ops::DerefMut;

use hashlink::linked_hash_map::RawOccupiedEntryMut;

use crate::meter::Meter;
use crate::LruCache;

pub struct PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    S: BuildHasher,
    M: Meter<K, V>,
{
    entry: RawOccupiedEntryMut<'a, K, V>,
    lru: *mut LruCache<K, V, S, M>,
}

impl<'a, K, V, S, M> PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    S: BuildHasher,
    M: Meter<K, V>,
{
    pub(crate) fn new(
        entry: RawOccupiedEntryMut<'a, K, V>,
        lru: *mut LruCache<K, V, S, M>,
    ) -> Self {
        let lru = unsafe { &mut *lru };

        lru.measure_remove(entry.key(), entry.get());

        PeekMut { entry, lru }
    }
}

impl<'a, K, V, S, M> Debug for PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    V: Debug,
    S: BuildHasher,
    M: Meter<K, V>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("PeekMut").field(&self.deref()).finish()
    }
}

impl<'a, K, V, S, M> Deref for PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    S: BuildHasher,
    M: Meter<K, V>,
{
    type Target = V;

    fn deref(&self) -> &Self::Target {
        self.entry.get()
    }
}

impl<'a, K, V, S, M> DerefMut for PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    S: BuildHasher,
    M: Meter<K, V>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.entry.get_mut()
    }
}

impl<'a, K, V, S, M> Drop for PeekMut<'a, K, V, S, M>
where
    K: Eq + Hash,
    S: BuildHasher,
    M: Meter<K, V>,
{
    fn drop(&mut self) {
        let lru = unsafe { &mut *self.lru };
        lru.measure_add(self.entry.key(), self.entry.get());

        lru.evict_by_policy();
    }
}
