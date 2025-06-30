use core::{
    borrow::Borrow,
    fmt,
    hash::{BuildHasher, Hash},
    iter,
    mem::{self, size_of},
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};

use crate::alloc::{alloc, boxed::Box, sync::Arc};

// NOTE: using 64 entries per subtrie... Should also try 32..

// TODO: do we actually need the clone bound here? Makes things messy.

#[derive(Clone)]
pub struct HashArrayMappedTrie<K, V, S> {
    len: usize,
    root: Arc<SparseArray<Entry<(K, V)>>>,
    build_hasher: Arc<S>,
}

impl<K, V, S: Default> Default for HashArrayMappedTrie<K, V, S> {
    fn default() -> Self {
        Self {
            len: 0,
            root: SparseArray::empty(),
            build_hasher: Arc::new(S::default()),
        }
    }
}

impl<K, V, S> HashArrayMappedTrie<K, V, S> {
    const MAX_LEVEL: usize = u64::BITS as usize / Bitmap::SHIFT;

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<K, V, S> HashArrayMappedTrie<K, V, S>
where
    K: Clone + Hash + Eq,
    V: Clone,
    S: BuildHasher,
{
    pub fn insert(&mut self, key: K, value: V) {
        let hash = make_hash(&*self.build_hasher, &key);
        Self::insert_impl(key, value, hash, &mut self.root, hash, 0);
        self.len += 1;
    }

    fn insert_impl(
        key: K,
        value: V,
        full_hash: u64,
        mut trie: &mut Arc<SparseArray<Entry<(K, V)>>>,
        mut hash: u64,
        mut level: usize,
    ) {
        loop {
            debug_assert!(level <= Self::MAX_LEVEL);

            let index = Bitmap::hash_to_index(hash);
            match trie.bitmap.index_of(index) {
                Ok(idx) => {
                    // The entry in the subtrie is occupied. Replace it.
                    let trie_mut = SparseArray::make_mut(trie);
                    let entry = &mut trie_mut.entries[idx];
                    match entry {
                        Entry::Subtrie(next_trie) => trie = next_trie,
                        Entry::Leaf {
                            hash: leaf_hash,
                            data: (leaf_key, leaf_value),
                        } => {
                            *entry = if level == Self::MAX_LEVEL {
                                // Equal hashes at the top level creates a collision node.
                                // The full hashes are equal here since we've exhausted our hash
                                // bits at the max level.
                                debug_assert_eq!(*leaf_hash, full_hash);
                                let data = ArcSlice::new(
                                    2,
                                    [(key, value), (leaf_key.clone(), leaf_value.clone())]
                                        .into_iter(),
                                );
                                Entry::Collision {
                                    hash: full_hash,
                                    data,
                                }
                            } else {
                                // Otherwise create a new subtrie and insert the old leaf and the
                                // new data into that.
                                let mut subtrie = SparseArray::empty();
                                Self::insert_impl(
                                    leaf_key.clone(),
                                    leaf_value.clone(),
                                    *leaf_hash,
                                    &mut subtrie,
                                    *leaf_hash >> (Bitmap::SHIFT * level),
                                    level,
                                );
                                Self::insert_impl(key, value, full_hash, &mut subtrie, hash, level);
                                Entry::Subtrie(subtrie)
                            };
                            return;
                        }
                        Entry::Collision {
                            hash: leaf_hash,
                            data,
                        } => {
                            // Update the collision node to prepend the new key-value pair.
                            debug_assert_eq!(*leaf_hash, full_hash);
                            let new_data = ArcSlice::new(
                                data.len() + 1,
                                iter::once((key, value)).chain(data.iter().cloned()),
                            );
                            let new_entry = Entry::Collision {
                                hash: full_hash,
                                data: new_data,
                            };
                            *entry = new_entry;
                            return;
                        }
                    }
                }
                Err(idx) => {
                    // Insert a new leaf node in the trie.
                    let bitmap = trie.bitmap.set(index);
                    let (before, after) = trie.entries.split_at(idx);
                    let entries = before
                        .iter()
                        .cloned()
                        .chain(iter::once(Entry::Leaf {
                            hash: full_hash,
                            data: (key, value),
                        }))
                        .chain(after.iter().cloned());
                    *trie = SparseArray::new(bitmap, entries);
                    return;
                }
            }

            level += 1;
            hash >>= Bitmap::SHIFT;
        }
    }
}

impl<K, V, S> HashArrayMappedTrie<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    /// Gets the key-value pairs for all instances of the key in the bag.
    ///
    /// Note that the main work done by this iterator is done in this function rather than the
    /// iterator: `get` is more expensive than iteration.
    pub fn get<'key, 'map: 'key, Q>(
        &'map self,
        key: &'key Q,
    ) -> impl Iterator<Item = (&'map K, &'map V)> + 'key
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hash = make_hash(&*self.build_hasher, key);
        let mut trie = &self.root;
        let mut level = 0;

        loop {
            debug_assert!(level <= Self::MAX_LEVEL);

            match trie.get(Bitmap::hash_to_index(hash)) {
                Some(entry) => match entry {
                    Entry::Subtrie(next_trie) => trie = next_trie,
                    Entry::Leaf { data: (k, v), .. } => {
                        // NOTE: is the equality check necessary? It's unlikely, but theoretically a
                        // nonexistent key could collide with a real key, so we need to be diligent
                        // and check that they actually _are_ equal.
                        let value = if k.borrow() == key {
                            Some((k, v))
                        } else {
                            None
                        };
                        return GetAllIter::Value(value);
                    }
                    Entry::Collision { data, .. } => {
                        return GetAllIter::CollisionNode {
                            key,
                            inner: data.iter(),
                        }
                    }
                },
                None => return GetAllIter::Value(None),
            }

            level += 1;
            hash >>= Bitmap::SHIFT;
        }
    }
}

enum GetAllIter<'map, 'key, Q: ?Sized, K, V> {
    Value(Option<(&'map K, &'map V)>),
    CollisionNode {
        key: &'key Q,
        inner: slice::Iter<'map, (K, V)>,
    },
}

impl<'map, 'key, Q, K, V> Iterator for GetAllIter<'map, 'key, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Item = (&'map K, &'map V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Value(value) => value.take(),
            Self::CollisionNode { key, inner } => {
                let (k, v) = inner.next()?;
                if k.borrow() == *key {
                    Some((k, v))
                } else {
                    None
                }
            }
        }
    }
}

// `make_hash`is pulled from Hashbrown's `map` module
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

#[derive(Clone, Copy)]
#[repr(C)]
struct Bitmap(usize);

impl fmt::Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl Bitmap {
    const EMPTY: Self = Self(0);

    const MAX_ENTRIES: usize = usize::BITS as usize;
    const SHIFT: usize = usize::BITS.trailing_zeros() as usize;

    /// Convert a 64-bit hash value to an index in the bitmap.
    ///
    /// The range of the returned index is guaranteed to be valid for the bitmap: it will always
    /// be in the range `0..Bitmap::MAX_ENTRIES`.
    const fn hash_to_index(hash: u64) -> usize {
        // Bitwise equivalent to `hash % Self::MAX_ENTRIES`:
        let mask = (Self::SHIFT - 1) as u64;
        (hash & mask) as usize
    }

    const fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    const fn get(&self, index: usize) -> bool {
        debug_assert!(index < Self::MAX_ENTRIES);

        self.0 & (1 << index) != 0
    }

    fn set(self, index: usize) -> Self {
        debug_assert!(index < Self::MAX_ENTRIES);

        Self(self.0 | 1 << index)
    }

    /// Convert an index into the bitmap into an index of the sparse array.
    fn index_of(&self, index: usize) -> Result<usize, usize> {
        debug_assert!(index < Self::MAX_ENTRIES);
        let pop = self.0.wrapping_shl(usize::BITS - index as u32).count_ones() as usize;
        if self.get(index) {
            Ok(pop)
        } else {
            Err(pop)
        }
    }
}

// Supports 64 elements on 64-bit architecture (`Bitmap::BITS`)
#[repr(C)]
struct SparseArray<T> {
    bitmap: Bitmap,
    // NOTE: this makes this type a dynamically sized type so it must always be on the heap.
    entries: [T],
}

impl<T> SparseArray<T> {
    fn get(&self, index: usize) -> Option<&T> {
        match self.bitmap.index_of(index) {
            Ok(idx) => Some(&self.entries[idx]),
            Err(_) => None,
        }
    }

    fn empty() -> Arc<SparseArray<T>> {
        Self::new(Bitmap::EMPTY, iter::empty())
    }

    fn new<I: IntoIterator<Item = T>>(bitmap: Bitmap, entries: I) -> Arc<Self> {
        let len = bitmap.len();
        let layout = Self::layout(len);
        let nullable = unsafe { alloc::alloc(layout) };
        let ptr = match NonNull::new(nullable) {
            Some(ptr) => ptr.as_ptr(),
            None => alloc::handle_alloc_error(layout),
        };
        let ptr = ptr::slice_from_raw_parts_mut(ptr, len) as *mut Self;

        unsafe { ptr::addr_of_mut!((*ptr).bitmap).write(bitmap) }
        let entries_ptr = unsafe { ptr::addr_of_mut!((*ptr).entries) as *mut T };
        let mut i = 0;
        for entry in entries {
            unsafe { entries_ptr.add(i).write(entry) };
            i += 1;
        }
        assert_eq!(i, len);
        let boxed = unsafe { Box::from_raw(ptr) };
        boxed.into()
    }

    fn layout(len: usize) -> alloc::Layout {
        alloc::Layout::new::<Bitmap>()
            .extend(alloc::Layout::array::<T>(len).unwrap())
            .unwrap()
            .0
            .pad_to_align()
    }
}

impl<T: Clone> SparseArray<T> {
    fn make_mut(this: &mut Arc<Self>) -> &mut Self {
        // Need lexical borrows to fix this :/
        // TODO: check if edition 2024 improves this.
        if Arc::get_mut(this).is_some() {
            return Arc::get_mut(this).unwrap();
        }

        *this = Self::new(this.bitmap, this.entries.iter().cloned());
        // Ideally this would be get_mut_unchecked
        Arc::get_mut(this).unwrap()
    }
}

impl<T> Drop for SparseArray<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            for entry in &mut self.entries {
                let ptr = entry as *mut _;
                unsafe { ptr::drop_in_place(ptr) };
            }
        }
    }
}

#[derive(Clone)]
#[repr(C)]
enum Entry<T> {
    Leaf { hash: u64, data: T },
    Collision { hash: u64, data: ArcSlice<T> },
    Subtrie(Arc<SparseArray<Self>>),
}

// DSTs are a real pain :/
// Maybe a customizable DST wrapper makes more sense...
#[derive(Clone)]
struct ArcSlice<T>(Arc<[T]>);

impl<T> ArcSlice<T> {
    fn new<I: Iterator<Item = T>>(len: usize, elements: I) -> Self {
        let layout = alloc::Layout::array::<T>(len).unwrap().pad_to_align();
        let nullable = unsafe { alloc::alloc(layout) };
        let ptr = match NonNull::new(nullable) {
            Some(ptr) => ptr.as_ptr(),
            None => alloc::handle_alloc_error(layout),
        };
        let ptr = ptr::slice_from_raw_parts_mut(ptr, len) as *mut [T];
        let elements_ptr = unsafe { ptr::addr_of_mut!((*ptr)) as *mut T };
        let mut i = 0;
        for element in elements {
            unsafe { elements_ptr.add(i).write(element) };
            i += 1;
        }
        assert_eq!(i, len);
        let boxed = unsafe { Box::from_raw(ptr) };
        Self(boxed.into())
    }
}

impl<T> Deref for ArcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitmap() {
        assert_eq!(Bitmap::EMPTY.len(), 0);
        for idx in 0..Bitmap::MAX_ENTRIES {
            assert!(!Bitmap::EMPTY.get(idx));
            assert!(Bitmap::EMPTY.set(idx).get(idx));
        }

        let b = Bitmap::EMPTY.set(5).set(10);

        assert_eq!(b.len(), 2);
        assert_eq!(b.index_of(5), Ok(0));
        assert_eq!(b.index_of(7), Err(1));
        assert_eq!(b.index_of(10), Ok(1));
        assert_eq!(b.index_of(13), Err(2));
    }

    #[test]
    fn sparse_array() {
        let a = SparseArray::<()>::empty();
        assert_eq!(&a.entries, &[]);
        assert_eq!(a.get(0), None);

        let mut a = SparseArray::new(Bitmap::EMPTY.set(5).set(10), [123, 456]);
        assert_eq!(&a.entries, &[123, 456]);
        assert_eq!(a.get(0), None);
        assert_eq!(a.get(5), Some(&123));
        assert_eq!(a.get(7), None);
        assert_eq!(a.get(10), Some(&456));
        assert_eq!(a.get(13), None);

        let old_a = a.clone();
        let new_a = SparseArray::make_mut(&mut a);
        new_a.entries[1] = 789;
        assert_eq!(new_a.get(10), Some(&789));
        assert_eq!(old_a.entries[1], 456);
        assert_eq!(old_a.get(10), Some(&456));
        assert_eq!(a.entries[1], 789);
        assert_eq!(a.get(10), Some(&789));
    }

    type Hamt<K, V> = HashArrayMappedTrie<K, V, crate::DefaultHashBuilder>;

    #[test]
    fn hamt() {
        let mut map = Hamt::default();
        map.insert(1, 10);
        assert_eq!(map.get(&1).collect::<Vec<_>>(), [(&1, &10)]);
    }
}
