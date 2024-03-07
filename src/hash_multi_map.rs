use core::{
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

use hashbrown::raw::{RawIter, RawIterHash, RawTable};

/// A collection of key-value pairs - similar to a HashMap - which allows for duplicate keys.
///
/// Entire key-value pairs may be duplicated. Conceptually this is a lot like
/// `HashMap<K, Vec<V>>`. Multimaps are usually preferred in cases where there are few duplicates.
///
/// In Spellbook this type is used to represent the "WordList." Hunspell-like dictionaries are
/// defined as sets of "stems" and a collection of "flags" that apply to that stem. Some
/// dictionaries provide multiple definitions of a stem with different sets of flags. Naively
/// merging these stems is not correct: the flags in one set might prevent an affix from
/// compounding while another set of flags provides a different affix which supports compounding.
///
/// Internally this is built on Hashbrown's "raw" API - a set of tools for building Swiss tables.
pub struct HashMultiMap<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    table: RawTable<(K, V)>,
    build_hasher: S,
}

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

impl<K, V, S> HashMultiMap<K, V, S>
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

    pub fn get(&self, k: &K) -> Option<&V> {
        let hash = make_hash(&self.build_hasher, k);
        self.table.find(hash, |(p, _v)| p == k).map(|b| {
            // Here we tie the lifetime of self to the value.
            let r = unsafe { b.as_ref() };
            &r.1
        })
    }

    pub fn get_all<'a>(&'a self, k: &'a K) -> impl Iterator<Item = &'a V> + 'a {
        let hash = make_hash(&self.build_hasher, k);

        GetAllIter {
            // Here we tie the lifetime of self to the iter.
            inner: unsafe { self.table.iter_hash(hash) },
            key: k,
            marker: PhantomData,
        }
    }
}

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

pub struct GetAllIter<'a, K: Eq, V> {
    inner: RawIterHash<(K, V)>,
    key: &'a K,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K: Eq, V> Iterator for GetAllIter<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.inner.next() {
                Some(bucket) => {
                    // SAFETY: the creator of the iterator (`get_all`) ensures that the reference
                    // to the value outlives the RawTable. It also prevents concurrent
                    // modifications to the table.
                    let element = unsafe { bucket.as_ref() };
                    if self.key.eq(&element.0) {
                        return Some(&element.1);
                    }
                    continue;
                }
                None => return None,
            }
        }
    }
}
