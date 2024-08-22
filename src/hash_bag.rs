use core::{
    borrow::Borrow,
    fmt::Debug,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

use hashbrown::raw::{RawIter, RawIterHash, RawTable};

/// A collection of key-value pairs - similar to a HashMap - which allows for duplicate keys.
///
/// The name is inspired by Erlang's ETS bag table type which also allows duplicate records.
/// Entire key-value pairs may be duplicated. Conceptually this is a lot like
/// `HashMap<K, Vec<V>>`. In other languages like C++ this is called a [multimap].
/// Multimaps are usually preferred over `HashMap<K, Vec<V>>` in cases where there are few
/// duplicates since the overhead of the Vec is unnecessary in most lookups.
///
/// In Spellbook this type is used to represent the "WordList". Hunspell-like dictionaries are
/// defined as sets of "stems" and a collection of "flags" that apply to that stem. Some
/// dictionaries provide multiple definitions of a stem with different sets of flags. Naively
/// merging these stems is not correct: the flags in one set might prevent an affix from
/// compounding while another set of flags provides a different affix which supports compounding.
///
/// Internally this is built on Hashbrown's "raw" API - a set of tools for building [Swiss
/// Tables].
///
/// [multimap]: https://en.cppreference.com/w/cpp/container/multimap
/// [Swiss Tables]: https://abseil.io/blog/20180927-swisstables
pub struct HashBag<K, V, S> {
    table: RawTable<(K, V)>,
    build_hasher: S,
}

impl<K, V, S> HashBag<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    pub fn with_hasher(build_hasher: S) -> Self {
        Self {
            table: RawTable::new(),
            build_hasher,
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, build_hasher: S) -> Self {
        Self {
            table: RawTable::with_capacity(capacity),
            build_hasher,
        }
    }

    pub fn insert(&mut self, k: K, v: V) {
        let hash = make_hash(&self.build_hasher, &k);
        let hasher = make_hasher(&self.build_hasher);
        self.table.reserve(1, make_hasher(&self.build_hasher));
        // Insert without attempting to find an existing entry with this key.
        self.table.insert(hash, (k, v), hasher);
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        // Here we tie the lifetime of self to the iter.
        Iter {
            inner: unsafe { self.table.iter() },
            marker: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn get<'map, 'key, Q>(&'map self, k: &'key Q) -> GetAllIter<'map, 'key, Q, K, V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash = make_hash(&self.build_hasher, k);

        GetAllIter {
            // Here we tie the lifetime of self to the iter.
            inner: unsafe { self.table.iter_hash(hash) },
            key: k,
            marker: PhantomData,
        }
    }
}

impl<K, V, S> Debug for HashBag<K, V, S>
where
    K: Debug + Hash + Eq,
    V: Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

// Unused but maybe useful in the future:
/*
impl<K, V, S> Default for HashMultiMap<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher + Default,
{
    fn default() -> Self {
        Self {
            table: Default::default(),
            build_hasher: Default::default(),
        }
    }
}
impl<K, V, S> HashMultiMap<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher + Default,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            table: RawTable::with_capacity(capacity),
            build_hasher: Default::default(),
        }
    }
}
*/

// `make_hash`, `make_hasher`, and `Iter` are pulled from Hashbrown's `map` module
// at `274c7bbd79398881e0225c0133e423ce60d7a8f1`.

fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

fn make_hasher<Q, V, S>(hash_builder: &S) -> impl Fn(&(Q, V)) -> u64 + '_
where
    Q: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<Q, S>(hash_builder, &val.0)
}

pub struct Iter<'a, K, V> {
    inner: RawIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some(x) => unsafe {
                let r = x.as_ref();
                Some((&r.0, &r.1))
            },
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

pub struct GetAllIter<'map, 'key, Q: ?Sized, K, V>
where
    K: Borrow<Q>,
    Q: Hash + Eq,
{
    inner: RawIterHash<(K, V)>,
    key: &'key Q,
    marker: PhantomData<(&'map K, &'map V)>,
}

impl<'map, 'key, Q: ?Sized, K, V> Iterator for GetAllIter<'map, 'key, Q, K, V>
where
    K: Borrow<Q>,
    Q: Hash + Eq,
{
    type Item = (&'map K, &'map V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.inner.next() {
                Some(bucket) => {
                    // SAFETY: the creator of the iterator (`get`) ensures that the reference
                    // to the value outlives the RawTable. It also prevents concurrent
                    // modifications to the table.
                    let element = unsafe { bucket.as_ref() };
                    if self.key.eq(element.0.borrow()) {
                        return Some((&element.0, &element.1));
                    }
                    continue;
                }
                None => return None,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::alloc::{string::ToString, vec::Vec};

    use super::*;

    #[test]
    fn insert_and_get_duplicate_keys() {
        let mut map = HashBag::with_hasher(ahash::RandomState::new());
        map.insert(1, 1);
        map.insert(5, 5);
        assert!(map.len() == 2);
        map.insert(1, 2);
        assert!(map.len() == 3);

        let mut vals: Vec<_> = map.get(&1).map(|kv| kv.1).copied().collect();
        vals.sort_unstable();
        assert_eq!(&[1, 2], vals.as_slice());
        let vals = map.get(&5).map(|kv| kv.1).copied().collect::<Vec<_>>();
        assert_eq!(&[5], vals.as_slice());
    }

    #[test]
    fn string_keys() {
        let mut map = HashBag::with_hasher(ahash::RandomState::new());
        map.insert("hello".to_string(), "bob");
        map.insert("hello".to_string(), "world");
        map.insert("bye".to_string(), "bob");

        let mut hellos: Vec<_> = map.get("hello").map(|kv| kv.1).copied().collect();
        hellos.sort_unstable();
        assert_eq!(&["bob", "world"], hellos.as_slice());

        let vals: Vec<_> = map.get("bye").map(|kv| kv.1).copied().collect();
        assert_eq!(&["bob"], vals.as_slice());
    }

    #[test]
    fn iter() {
        // The iterator is currently unused but very small and could be useful for debugging.
        let pairs = &[(1, 1), (1, 2), (1, 3), (3, 1)];
        let mut map = HashBag::with_capacity_and_hasher(pairs.len(), ahash::RandomState::new());
        for (k, v) in pairs {
            map.insert(k, v);
        }

        assert_eq!(map.iter().len(), pairs.len());

        let mut values: Vec<_> = map.iter().map(|(k, v)| (**k, **v)).collect();
        values.sort_unstable();
        assert_eq!(&values, pairs);
    }
}
