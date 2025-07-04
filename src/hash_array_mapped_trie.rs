use core::{
    borrow::Borrow,
    fmt,
    hash::{BuildHasher, Hash},
    iter, mem,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};

use crate::alloc::{alloc, sync::Arc, vec, vec::Vec};

#[derive(Clone, Default)]
pub struct HashArrayMappedTrie<K, V, S> {
    len: usize,
    root: Arc<SparseArray<Entry<(K, V)>>>,
    build_hasher: Arc<S>,
}

impl<K, V, S> HashArrayMappedTrie<K, V, S> {
    // How many times we can use and then shift the number of hash bits.
    const MAX_LEVEL: usize = u64::BITS as usize / Bitmap::SHIFT;

    pub fn with_hasher(build_hasher: S) -> Self {
        Self {
            len: Default::default(),
            root: Default::default(),
            build_hasher: Arc::new(build_hasher),
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn iter(&self) -> Iter<K, V> {
        let root = TrieNodeIter::Entries(self.root.entries().iter());
        Iter { stack: vec![root] }
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

            level += 1;
            hash >>= Bitmap::SHIFT;

            match trie.bitmap().index_of(index) {
                Ok(idx) => {
                    // The entry in the subtrie is occupied. Replace it.
                    let trie_mut = Arc::make_mut(trie);
                    let entry = &mut trie_mut.entries_mut()[idx];
                    match entry {
                        Entry::Subtrie(next_trie) => trie = next_trie,
                        Entry::Leaf {
                            hash: leaf_hash,
                            data: (leaf_key, leaf_value),
                        } => {
                            *entry = if level == Self::MAX_LEVEL {
                                // Equal hashes at the top level creates a collision node.
                                let data = ArcSlice::new(
                                    2,
                                    [(key, value), (leaf_key.clone(), leaf_value.clone())],
                                );
                                Entry::Collision { data }
                            } else {
                                // Otherwise replace the leaf with a new subtrie containing a leaf
                                // for the key-value pair and insert the old leaf into that.
                                let mut subtrie = Arc::new(SparseArray::new(
                                    Bitmap::EMPTY.set(Bitmap::hash_to_index(hash)),
                                    [Entry::Leaf {
                                        hash: full_hash,
                                        data: (key, value),
                                    }],
                                ));
                                Self::insert_impl(
                                    leaf_key.clone(),
                                    leaf_value.clone(),
                                    *leaf_hash,
                                    &mut subtrie,
                                    *leaf_hash >> (Bitmap::SHIFT * level),
                                    level,
                                );
                                Entry::Subtrie(subtrie)
                            };
                            return;
                        }
                        Entry::Collision { data } => {
                            // Update the collision node to prepend the new key-value pair.
                            let new_data = ArcSlice::new(
                                data.len() + 1,
                                iter::once((key, value)).chain(data.iter().cloned()),
                            );
                            let new_entry = Entry::Collision { data: new_data };
                            *entry = new_entry;
                            return;
                        }
                    }
                }
                Err(idx) => {
                    // Insert a new leaf node in the trie.
                    let bitmap = trie.bitmap().set(index);
                    let (before, after) = trie.entries().split_at(idx);
                    let entries = before
                        .iter()
                        .cloned()
                        .chain(iter::once(Entry::Leaf {
                            hash: full_hash,
                            data: (key, value),
                        }))
                        .chain(after.iter().cloned());
                    *trie = Arc::new(SparseArray::new(bitmap, entries));
                    return;
                }
            }
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
        Q: Hash + Eq + ?Sized + fmt::Debug,
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
                        // NOTE: is the equality check necessary? It's unlikely, but theoretically
                        // a nonexistent key could collide with a real key, so we need to be
                        // diligent and check that they actually _are_ equal.
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

    // Helper to act more like a standard dictionary-like type, used just for tests.
    #[cfg(test)]
    pub fn get_one<'key, 'map: 'key, Q>(&'map self, key: &'key Q) -> Option<&'map V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized + fmt::Debug,
    {
        self.get(key).next().map(|(k, v)| {
            assert_eq!(k.borrow(), key);
            v
        })
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

enum TrieNodeIter<'a, T> {
    Entries(slice::Iter<'a, Entry<T>>),
    Values(slice::Iter<'a, T>),
}

pub struct Iter<'a, K, V> {
    stack: Vec<TrieNodeIter<'a, (K, V)>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // The iterator is implemented by depth-first search. This is a small spin on the very
        // classic DFS approach which uses a stack of iterators - this works well for collision
        // nodes.
        // See the bottom of <https://en.wikipedia.org/wiki/Depth-first_search#Pseudocode>.
        loop {
            match self.stack.last_mut()? {
                TrieNodeIter::Entries(entries) => match entries.next() {
                    Some(entry) => match entry {
                        Entry::Leaf { data, .. } => return Some(data),
                        Entry::Collision { data } => {
                            self.stack.push(TrieNodeIter::Values(data.iter()));
                        }
                        Entry::Subtrie(trie) => {
                            self.stack
                                .push(TrieNodeIter::Entries(trie.entries().iter()));
                        }
                    },
                    None => {
                        self.stack.pop();
                    }
                },
                TrieNodeIter::Values(values) => match values.next() {
                    Some(v) => return Some(v),
                    None => {
                        self.stack.pop();
                    }
                },
            }
        }
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct Bitmap(usize);

impl fmt::Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl Bitmap {
    const EMPTY: Self = Self(0);

    const BITS: u32 = usize::BITS;
    const MAX_ENTRIES: usize = usize::BITS as usize;
    /// The number of bits to consume of a hash to find an index in the bitmap.
    const SHIFT: usize = Self::MAX_ENTRIES.ilog2() as usize;

    /// Convert a 64-bit hash value to an index in the bitmap.
    ///
    /// The range of the returned index is guaranteed to be valid for the bitmap: it will always
    /// be in the range `0..Bitmap::MAX_ENTRIES`.
    const fn hash_to_index(hash: u64) -> usize {
        // Bitwise equivalent to `hash % Self::MAX_ENTRIES`:
        const MASK: u64 = ((1 << Bitmap::SHIFT) - 1) as u64;
        (hash & MASK) as usize
    }

    const fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    const fn is_set(&self, index: usize) -> bool {
        debug_assert!(index < Self::MAX_ENTRIES);

        self.0 & (1 << index) != 0
    }

    const fn set(self, index: usize) -> Self {
        debug_assert!(index < Self::MAX_ENTRIES);

        Self(self.0 | 1 << index)
    }

    /// Convert an index into the bitmap into an index of the sparse array.
    fn index_of(&self, index: usize) -> Result<usize, usize> {
        debug_assert!(index < Self::MAX_ENTRIES);

        let bits_under_index = Self::BITS - index as u32;
        let pop = if bits_under_index < Self::BITS {
            (self.0 << bits_under_index).count_ones() as usize
        } else {
            0
        };

        if self.is_set(index) {
            Ok(pop)
        } else {
            Err(pop)
        }
    }
}

#[repr(C)]
struct SparseArrayInner<T> {
    /// A bitmap describing which indices in the sparse array are allocated.
    ///
    /// For example if a bitmap has only the fifth bit set, then the `entries` array below will
    /// be allocated with that one entry. Looking up index 5 would return that entry and any other
    /// index would return `None`.
    bitmap: Bitmap,
    /// The entries in the sparse array.
    ///
    /// This field has room for between zero and `Bitmap::MAX_ENTRIES` depending on how many slots
    /// are occupied.
    ///
    /// A sparse array with one index set has one entry at this location - no matter what index in
    /// the bitmap is set. When there are multiple indices set in the bitmap, the entries here
    /// are stored consecutively so that the least significant set bit comes first, then the next
    /// most significant and so on. If a sparse array is full then
    entries: [T; 0],
}

struct SparseArray<T> {
    ptr: NonNull<SparseArrayInner<T>>,
}

unsafe impl<T> Sync for SparseArray<T> {}
unsafe impl<T> Send for SparseArray<T> {}

impl<T> SparseArray<T> {
    fn bitmap(&self) -> Bitmap {
        let ptr = self.ptr.as_ptr();
        unsafe { ptr.read().bitmap }
    }

    fn entries(&self) -> &[T] {
        let len = self.bitmap().len();
        let ptr = self.ptr.as_ptr();
        let entries = unsafe { ptr::addr_of!((*ptr).entries).cast() };
        unsafe { slice::from_raw_parts(entries, len) }
    }

    fn entries_mut(&mut self) -> &mut [T] {
        let len = self.bitmap().len();
        let ptr = self.ptr.as_ptr();
        let entries = unsafe { ptr::addr_of_mut!((*ptr).entries).cast() };
        unsafe { slice::from_raw_parts_mut(entries, len) }
    }

    fn get(&self, index: usize) -> Option<&T> {
        match self.bitmap().index_of(index) {
            Ok(idx) => Some(&self.entries()[idx]),
            Err(_) => None,
        }
    }

    fn new<I: IntoIterator<Item = T>>(bitmap: Bitmap, entries: I) -> Self {
        let len = bitmap.len();
        let layout = Self::layout(len);
        let nullable = unsafe { alloc::alloc(layout) };
        let non_null = match NonNull::new(nullable) {
            Some(ptr) => ptr.cast::<SparseArrayInner<T>>(),
            None => alloc::handle_alloc_error(layout),
        };

        let ptr = non_null.as_ptr();
        unsafe { ptr::addr_of_mut!((*ptr).bitmap).write(bitmap) };
        let mut entries_ptr = unsafe { ptr::addr_of_mut!((*ptr).entries).cast::<T>() };
        let mut i = 0;
        for entry in entries {
            unsafe { entries_ptr.write(entry) };
            entries_ptr = unsafe { entries_ptr.add(1) };
            i += 1;
        }
        assert_eq!(i, len);

        Self { ptr: non_null }
    }

    fn layout(len: usize) -> alloc::Layout {
        alloc::Layout::new::<Bitmap>()
            // .align_to(align_of::<T>())
            // .unwrap()
            // .pad_to_align()
            .extend(alloc::Layout::array::<T>(len).unwrap())
            .unwrap()
            .0
            .pad_to_align()
    }
}

impl<T> Default for SparseArray<T> {
    fn default() -> Self {
        Self::new(Bitmap::EMPTY, iter::empty())
    }
}

impl<T: Clone> Clone for SparseArray<T> {
    fn clone(&self) -> Self {
        Self::new(self.bitmap(), self.entries().iter().cloned())
    }
}

impl<T> Drop for SparseArray<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            for entry in self.entries_mut() {
                let ptr = entry as *mut _;
                unsafe { ptr::drop_in_place(ptr) };
            }
        }
        let layout = Self::layout(self.bitmap().len());
        unsafe { alloc::dealloc(self.ptr.as_ptr().cast(), layout) }
    }
}

impl<T: fmt::Debug> fmt::Debug for SparseArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        map.entry(&"bitmap", &self.bitmap());
        let mut entries = self.entries().iter();
        for idx in 0..self.bitmap().len() {
            if self.bitmap().is_set(idx) {
                map.entry(&idx, &entries.next().unwrap());
            }
        }
        map.finish()
    }
}

#[derive(Clone, Debug)]
#[repr(C)]
enum Entry<T> {
    Leaf { hash: u64, data: T },
    Collision { data: ArcSlice<T> },
    Subtrie(Arc<SparseArray<Self>>),
}

#[derive(Clone, Debug)]
struct ArcSlice<T>(Arc<[T]>);

impl<T> ArcSlice<T> {
    fn new<I: IntoIterator<Item = T>>(len: usize, elements: I) -> Self {
        let mut vec = Vec::new();
        vec.reserve_exact(len);
        vec.extend(elements);
        assert_eq!(vec.len(), len);
        assert_eq!(vec.capacity(), len);
        Self(vec.into())
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
            assert!(!Bitmap::EMPTY.is_set(idx));
            assert!(Bitmap::EMPTY.set(idx).is_set(idx));
        }

        assert_eq!(Bitmap::hash_to_index(1), 1);
        assert_eq!(Bitmap::hash_to_index(Bitmap::MAX_ENTRIES as u64 + 1), 1);
        for n in 0..10_000 {
            assert_eq!(
                Bitmap::hash_to_index(n),
                (n % Bitmap::MAX_ENTRIES as u64) as usize
            );
        }

        let b = Bitmap::EMPTY.set(5).set(10);
        assert_eq!(b.len(), 2);
        assert_eq!(b.index_of(5), Ok(0));
        assert_eq!(b.index_of(7), Err(1));
        assert_eq!(b.index_of(10), Ok(1));
        assert_eq!(b.index_of(13), Err(2));

        let b = Bitmap::EMPTY.set(1);
        assert_eq!(b.len(), 1);
        assert_eq!(b.index_of(1), Ok(0));
        assert_eq!(b.index_of(5), Err(1));

        let b = Bitmap::EMPTY.set(0);
        assert_eq!(b.len(), 1);
        assert_eq!(b.index_of(0), Ok(0));
        assert_eq!(b.index_of(5), Err(1));
    }

    #[test]
    fn sparse_array() {
        let a = SparseArray::<usize>::default();
        assert_eq!(a.bitmap().len(), 0);
        assert_eq!(a.entries(), &[]);
        assert_eq!(a.get(0), None);

        let a = SparseArray::new(Bitmap::EMPTY.set(5).set(10), [123, 456]);
        assert_eq!(a.entries(), &[123, 456]);
        assert_eq!(a.get(0), None);
        assert_eq!(a.get(5), Some(&123));
        assert_eq!(a.get(7), None);
        assert_eq!(a.get(10), Some(&456));
        assert_eq!(a.get(13), None);
    }

    #[test]
    fn sparse_array_size() {
        // It's always a thin pointer - must be the same size as a pointer.
        assert_eq!(size_of::<SparseArray<usize>>(), size_of::<usize>());
        assert_eq!(size_of::<SparseArray<u8>>(), size_of::<usize>());
        assert_eq!(size_of::<SparseArray<u128>>(), size_of::<usize>());
    }

    #[test]
    fn sparse_array_alignment() {
        let bitmap = Bitmap::EMPTY.set(5).set(10);
        assert_eq!(bitmap.len(), 2);

        // Same size:
        assert_eq!(size_of::<Bitmap>(), size_of::<usize>());
        let mut a = SparseArray::<usize>::new(bitmap, [123, 456]);
        assert_eq!(a.entries(), &[123, 456]);
        a.entries_mut()[0] = 789;
        assert_eq!(a.get(5), Some(&789));

        // Inner type is smaller:
        assert!(size_of::<Bitmap>() > size_of::<u8>());
        let mut a = SparseArray::<u8>::new(bitmap, [12, 34]);
        assert_eq!(a.entries(), &[12, 34]);
        a.entries_mut()[0] = 56;
        assert_eq!(a.get(5), Some(&56));

        // Inner type is larger:
        assert!(size_of::<Bitmap>() < size_of::<u128>());
        let mut a = SparseArray::<u128>::new(bitmap, [123, 456]);
        assert_eq!(a.entries(), &[123, 456]);
        a.entries_mut()[0] = 789;
        assert_eq!(a.get(5), Some(&789));
    }

    type Hamt<K, V> = HashArrayMappedTrie<K, V, crate::DefaultHashBuilder>;

    impl<K: Ord, V: Ord, S> HashArrayMappedTrie<K, V, S> {
        fn sorted_entries(&self) -> Vec<&(K, V)> {
            let mut entries: Vec<_> = self.iter().collect();
            entries.sort();
            entries
        }
    }

    #[test]
    fn hamt_basics() {
        let mut map = Hamt::default();
        map.insert(1, 10);
        assert_eq!(map.get_one(&1), Some(&10));
        map.insert(5, 5);
        assert_eq!(map.get_one(&5), Some(&5));
        assert_eq!(map.len(), 2);
        assert_eq!(map.sorted_entries(), [&(1, 10), &(5, 5)]);

        let mut map = Hamt::default();
        let len = Bitmap::MAX_ENTRIES * 10;
        for i in 0..len {
            map.insert(i, i);
            assert_eq!(map.get_one(&i), Some(&i));
        }
        assert_eq!(map.len(), len);
        let entries = map.sorted_entries();
        assert_eq!(entries.len(), len);
        for (i, entry) in entries.into_iter().enumerate() {
            assert_eq!(entry, &(i, i));
        }
    }

    #[test]
    fn hamt_persistent() {
        let mut map = Hamt::default();
        let old_map = map.clone();
        map.insert(1, 1);
        assert_eq!(map.get_one(&1), Some(&1));
        assert_eq!(map.len(), 1);
        assert_eq!(old_map.get_one(&1), None);
        assert_eq!(old_map.len(), 0);
    }
}
