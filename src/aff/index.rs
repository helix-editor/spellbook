use std::{
    collections::{hash_map::RandomState, HashMap},
    hash::{BuildHasher, Hash, Hasher},
};

/// An index type for affixes (prefixes & suffixes) allowing fast
/// lookup of substrings of a word.
// Currently this is implemented as a Trie backed by a HashMap.
// TODO: fxhash?
#[derive(Debug, Default, Clone)]
pub struct AffixIndex<T> {
    table: HashMap<u64, Option<T>>,
    hasher: RandomState,
}

// The trie relies heavily on
// Note [HashBuilder::finish] doesn't destroy the builder. It's more
// like we're popping out the hasher's value at that point in time.

impl<T> AffixIndex<T> {
    /// Insert the value into the index with `chars` as the lookup key.
    ///
    /// Takes time proportional to the cardinality of `chars`.
    #[cfg(test)]
    pub(crate) fn insert<I: Iterator<Item = char>>(&mut self, chars: I, value: T) {
        let mut chars = chars.peekable();
        let mut hash_state = self.hasher.build_hasher();
        while let Some(ch) = chars.next() {
            ch.hash(&mut hash_state);
            let hash = hash_state.finish();
            let maybe_value = self.table.entry(hash).or_insert_with(Default::default);
            if chars.peek().is_none() {
                *maybe_value = Some(value);
                // The break is redundant but satisfies the borrow checker
                // that T is not moved multiple times.
                // TODO: rewrite as a do-while to make this cleaner?
                break;
            }
        }
    }

    /// Looks up the value in the index, even if the lookup `chars` are
    /// longer than any key in the trie.
    ///
    /// Takes time proportional to the cardinality of `chars`.
    pub(crate) fn get<I: Iterator<Item = char>>(&self, chars: I) -> Option<&T> {
        let mut chars = chars.peekable();
        let mut value = None;
        let mut hash_state = self.hasher.build_hasher();

        while let Some(ch) = chars.next() {
            ch.hash(&mut hash_state);
            let hash = hash_state.finish();
            let maybe_value = match self.table.get(&hash) {
                Some(maybe_value) => maybe_value,
                None => return value,
            };
            if chars.peek().is_none() {
                return maybe_value.as_ref();
            }
            value = maybe_value.as_ref();
        }

        value
    }
}

impl<T> AffixIndex<Vec<T>> {
    /// Inserts the value into the [Vec] entry in the trie if it exists, creating
    /// a single-element Vec at the entry otherwise.
    pub(crate) fn push<I: Iterator<Item = char>>(&mut self, chars: I, value: T) {
        // The Entry API is a good chunk of code to add so this will suffice
        // since we know exactly how this type will be used in parsing.
        let mut chars = chars.peekable();
        let mut hash_state = self.hasher.build_hasher();
        while let Some(ch) = chars.next() {
            ch.hash(&mut hash_state);
            let hash = hash_state.finish();
            let maybe_value = self.table.entry(hash).or_insert_with(Default::default);
            if chars.peek().is_none() {
                match maybe_value.as_mut() {
                    Some(values) => values.push(value),
                    None => *maybe_value = Some(vec![value]),
                }
                break;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sanity_check_test() {
        let mut index: AffixIndex<usize> = Default::default();
        assert_eq!(index.get("abc".chars()), None);

        index.insert("abc".chars(), 123);
        assert_eq!(index.get("abc".chars()), Some(&123));
        assert_eq!(index.get("def".chars()), None);
    }

    /// The trie should return prefixes for entire words.
    /// For example "re" should match "retry".
    #[test]
    fn longer_needle_than_haystack() {
        let mut index: AffixIndex<usize> = Default::default();
        index.insert("re".chars(), 1);

        assert_eq!(index.get("retry".chars()), Some(&1));
        assert_eq!(index.get("terminate".chars()), None);
    }

    /// Check that even if we're looking up the same char at the
    /// same depth ('c' at depth 2 (zero-indexed) in this case),
    /// the lookup doesn't collide with any other entry which
    /// uses that same char at the same depth.
    #[test]
    fn depth_and_char_collision_test() {
        let mut index: AffixIndex<usize> = Default::default();
        index.insert("abc".chars(), 123);
        index.insert("bac".chars(), 213);

        assert_eq!(index.get("abc".chars()), Some(&123));
        assert_eq!(index.get("bac".chars()), Some(&213));
    }
}
