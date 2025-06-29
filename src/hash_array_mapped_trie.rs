use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    iter,
    mem::{self, size_of},
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};

use crate::alloc::{alloc, boxed::Box, sync::Arc, vec::Vec};

// NOTE: using 64 entries per subtrie... Should also try 32..

// TODO: do we actually need the clone bound here? Makes things messy.

pub struct HashArrayMappedTrie<K: Clone, V: Clone, S> {
    len: usize,
    root: Arc<SparseArray<Entry<(K, V)>>>,
    build_hasher: Arc<S>,
}

impl<K: Clone, V: Clone, S> HashArrayMappedTrie<K, V, S> {
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<K: Clone, V: Clone, S: Default> Default for HashArrayMappedTrie<K, V, S> {
    fn default() -> Self {
        Self {
            len: 0,
            root: SparseArray::empty(),
            build_hasher: Arc::new(S::default()),
        }
    }
}

impl<K, V, S> HashArrayMappedTrie<K, V, S>
where
    K: Clone + Hash + Eq,
    V: Clone + Hash,
    S: BuildHasher,
{
    const SHIFT: usize = size_of::<usize>();
    const MAX_LEVEL: usize = size_of::<usize>();

    pub fn insert(&mut self, key: K, value: V) {
        let hash = make_hash(&*self.build_hasher, &key);
        Self::insert_impl(key, value, hash, &mut self.root, hash, 0);
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

            let index = shift_hash(hash);
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
                                    hash,
                                    level,
                                );
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
            hash >>= Self::SHIFT;
        }
    }

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

            match trie.get(shift_hash(hash)) {
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
                            data,
                            index: 0,
                        }
                    }
                },
                None => return GetAllIter::Value(None),
            }

            level += 1;
            hash >>= Self::SHIFT;
        }
    }
}

enum GetAllIter<'map, 'key, Q: ?Sized, K, V> {
    Value(Option<(&'map K, &'map V)>),
    CollisionNode {
        key: &'key Q,
        data: &'map ArcSlice<(K, V)>,
        index: usize,
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
            Self::CollisionNode { key, data, index } => {
                let (k, v) = data.get(*index)?;
                if k.borrow() == *key {
                    *index += 1;
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

impl Bitmap {
    const EMPTY: Self = Self(0);

    const BITS: usize = usize::BITS as usize;

    const fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    const fn get(&self, index: usize) -> bool {
        debug_assert!(index < Self::BITS);

        self.0 & (1 << index) != 0
    }

    fn set(self, index: usize) -> Self {
        debug_assert!(index < Self::BITS);

        Self(self.0 | 1 << index)
    }

    fn clear(self, index: usize) -> Self {
        debug_assert!(index < Self::BITS);

        Self(self.0 & !(1 << index))
    }

    fn iter(self) -> BitmapIter {
        BitmapIter {
            bits: self,
            index: 0,
            len: self.len(),
        }
    }

    /// Convert an index into the bitmap into an index of the sparse array.
    fn index_of(&self, index: usize) -> Result<usize, usize> {
        debug_assert!(index < Self::BITS);
        let pop = (self.0 << index).count_ones() as usize;
        if self.get(index) {
            Ok(pop)
        } else {
            Err(pop)
        }
    }
}

struct BitmapIter {
    bits: Bitmap,
    index: usize,
    len: usize,
}

impl BitmapIter {
    fn remaining(&self) -> usize {
        (self.bits.0 >> self.index).count_ones() as usize
    }
}

impl Iterator for BitmapIter {
    // The index into entries
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.index > self.len {
                return None;
            }
            let idx = self.index;
            self.index += 1;
            if self.bits.get(idx) {
                return Some(idx);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for BitmapIter {
    fn len(&self) -> usize {
        self.remaining()
    }
}

const fn shift_hash(hash: u64) -> usize {
    // TODO: this should be done with shifts instead
    (hash % Bitmap::BITS as u64) as usize
}

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

    fn entries(&self) -> &[T] {
        let len = self.bitmap.len();
        let data = ptr::addr_of!(self.entries) as *const T;
        unsafe { slice::from_raw_parts(data, len) }
    }

    fn entries_mut(&mut self) -> &mut [T] {
        let len = self.bitmap.len();
        let data = ptr::addr_of_mut!(self.entries) as *mut T;
        unsafe { slice::from_raw_parts_mut(data, len) }
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

        *this = Self::clone(this);
        // Ideally this would be get_mut_unchecked
        Arc::get_mut(this).unwrap()
    }

    fn clone(this: &Arc<Self>) -> Arc<Self> {
        Self::new(this.bitmap, this.entries().iter().cloned())
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
    }
}

// fn clone(&self) -> Self {
//     Self::new(self.bitmap, self.entries.iter().cloned())
// }

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
        for idx in 0..Bitmap::BITS {
            assert!(!Bitmap::EMPTY.get(idx));
            assert!(Bitmap::EMPTY.set(idx).get(idx));
        }
    }

    #[test]
    fn sparse_array() {
        let a = SparseArray::<()>::empty();
        assert_eq!(a.entries(), &[]);
        assert_eq!(a.get(0), None);

        // let a = SparseArray::new(Bitmap::, [5, 10]);
    }
}
