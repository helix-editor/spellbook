use core::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    iter,
    mem::{self, size_of},
    ptr::{self, NonNull},
    slice,
};

use crate::alloc::{alloc, boxed::Box, sync::Arc, vec::Vec};

// NOTE: using 64 entries per subtrie... Should also try 32..

pub struct HashArrayMappedTrie<K: Clone, V: Clone, S> {
    len: usize,
    root: Entry<(K, V)>,
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
            root: Entry::Subtrie(Subtrie::empty()),
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
    pub fn insert(&mut self, k: K, v: V) {
        todo!()
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
        const SHIFT: usize = size_of::<usize>();
        const MAX_LEVEL: usize = size_of::<usize>();

        let mut hash = make_hash(&*self.build_hasher, key);
        let mut entry = &self.root;
        let mut level = 0;

        loop {
            debug_assert!(level <= MAX_LEVEL);

            match entry {
                Entry::Subtrie(subtrie) => {
                    // Generally this branch should be the hottest.

                    // TODO: this should be done with shifts instead
                    let index = (hash % Bitmap::BITS as u64) as usize;
                    match subtrie.get(index) {
                        Some(next_entry) => entry = next_entry,
                        None => return GetAllIter::Value(None),
                    }
                }
                Entry::Value((k, v)) => {
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
                Entry::Collision(node) => {
                    // This branch is likely if a key actually does have multiple values in the
                    // bag. Iterate over the values. It should be less likely than singular
                    // K-V pairs though if we assume that accidental collisions are unlikely and
                    // that duplicate keys are also somewhat rare.
                    return GetAllIter::CollisionNode {
                        key,
                        node,
                        // TODO: fast-forward here to the first value, if there is one?
                        index: 0,
                    };
                }
            }

            level += 1;
            hash >>= SHIFT;
        }
    }
}

enum GetAllIter<'map, 'key, Q: ?Sized, K, V> {
    Value(Option<(&'map K, &'map V)>),
    CollisionNode {
        key: &'key Q,
        node: &'map CollisionNode<(K, V)>,
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
            Self::CollisionNode { key, node, index } => {
                let (k, v) = node.values.get(*index)?;
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

    // TODO: this needs some sanity unit testing. I think a `- 1` could be necessary here based
    // on the OTP source.
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

#[repr(C)]
struct Subtrie<T> {
    bitmap: Bitmap,
    // NOTE: this makes this type a dynamically sized type so it must always be on the heap.
    entries: [T],
}

impl<T> Subtrie<T> {
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

    fn empty() -> Arc<Subtrie<T>> {
        Self::new(Bitmap::EMPTY, iter::empty())
    }

    fn new<I: ExactSizeIterator<Item = T>>(bitmap: Bitmap, entries: I) -> Arc<Self> {
        let len = bitmap.len();
        assert_eq!(bitmap.len(), entries.len());

        let layout = Self::layout(len);
        let nullable = unsafe { alloc::alloc(layout) };
        let ptr = match NonNull::new(nullable) {
            Some(ptr) => ptr.as_ptr(),
            None => alloc::handle_alloc_error(layout),
        };
        let ptr = ptr::slice_from_raw_parts_mut(ptr, len) as *mut Self;

        unsafe { ptr::addr_of_mut!((*ptr).bitmap).write(bitmap) }
        let entries_ptr = unsafe { ptr::addr_of_mut!((*ptr).entries) as *mut T };
        for (i, entry) in entries.enumerate() {
            unsafe { entries_ptr.add(i).write(entry) };
        }
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

impl<T> Drop for Subtrie<T> {
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
enum Entry<T: Clone> {
    Value(T),
    Collision(Arc<CollisionNode<T>>),
    Subtrie(Arc<Subtrie<Self>>),
}

/// When two keys have exactly the same hash they must share nodes.
#[derive(Clone)]
struct CollisionNode<T> {
    // hash? why do they store the hash?
    // Arc<[T]>?
    values: Vec<T>,
}
