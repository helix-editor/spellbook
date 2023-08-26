//! A radix tree implementation specialized for looking up affixes
//! by their affix/add text.

use std::{
    collections::{
        hash_map::{DefaultHasher, RandomState},
        HashMap,
    },
    hash::{BuildHasher, Hash, Hasher},
};

/// An index type for affixes (prefixes & suffixes) allowing fast
/// lookup of substrings of a word.
///
/// When read, it returns all values stored in the tree which the key
/// touches. For example you might store suffixes for "s", "ions",
/// and "ications", which all overlap. We can efficiently store all
/// three in this trie. [AffixIndex::get], when accessed with a word
/// like "complications", will return all the values stored for "s",
/// "ions", and "ications", while a word like "scions" will return
/// values from "s" and "ions".
#[derive(Debug, Clone)]
pub(crate) struct AffixIndex<T> {
    // Currently this is implemented as a Trie backed by a HashMap.
    table: HashMap<u64, Vec<T>>,
    hasher: RandomState,
}

/// The derive derivation of Default for AffixIndex mistakenly thinks
/// it needs a Default implementation for T. We can trick it by using
/// even more Default!
impl<T> Default for AffixIndex<T> {
    fn default() -> Self {
        Self {
            table: Default::default(),
            hasher: Default::default(),
        }
    }
}

// Note [HashBuilder::finish] doesn't destroy the builder. It's more
// like we're popping out the hasher's value at that point in time.

impl<T> AffixIndex<T> {
    /// Inserts the value into the [Vec] entry in the trie if it exists, creating
    /// a single-element Vec at the entry otherwise.
    pub(crate) fn push<I: Iterator<Item = char>>(&mut self, chars: I, value: T) {
        let mut chars = chars.peekable();
        let mut hash_state = self.hasher.build_hasher();
        while let Some(ch) = chars.next() {
            ch.hash(&mut hash_state);
            let hash = hash_state.finish();
            let values = self.table.entry(hash).or_insert_with(Default::default);
            if chars.peek().is_none() {
                values.push(value);
                break;
            }
        }
    }

    /// Looks up the value in the index, even if the lookup `chars` are
    /// longer than any key in the trie. Returns any `T` values stored in the
    /// trie along the path.
    pub(crate) fn get<I: Iterator<Item = char>>(&self, mut chars: I) -> impl Iterator<Item = &T> {
        use crate::stdx::EitherIterator::{Left, Right};

        match chars.next() {
            Some(char) => {
                let mut hasher = self.hasher.build_hasher();
                char.hash(&mut hasher);
                let hash = hasher.finish();

                Left(Get {
                    table: &self.table,
                    hasher,
                    hash,
                    char,
                    chars,
                    index: 0,
                })
            }
            None => Right(std::iter::empty()),
        }
    }
}

pub(crate) struct Get<'a, T, I: Iterator<Item = char>> {
    table: &'a HashMap<u64, Vec<T>>,
    hasher: DefaultHasher,
    hash: u64,
    char: char,
    chars: I,
    index: usize,
}

impl<'a, T, I: Iterator<Item = char>> Iterator for Get<'a, T, I> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self
                .table
                .get(&self.hash)
                .and_then(|values| values.get(self.index))
            {
                Some(value) => {
                    self.index += 1;
                    return Some(value);
                }
                None => {
                    self.char = self.chars.next()?;
                    self.char.hash(&mut self.hasher);
                    self.hash = self.hasher.finish();
                    self.index = 0;
                    continue;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn get<I: Iterator<Item = char>>(index: &AffixIndex<usize>, input: I) -> Vec<usize> {
        index.get(input).copied().collect()
    }

    #[test]
    fn sanity_check_test() {
        let mut index: AffixIndex<usize> = Default::default();
        assert_eq!(get(&index, "abc".chars()), vec![]);

        index.push("abc".chars(), 123);
        assert_eq!(get(&index, "abc".chars()), vec![123]);
        assert_eq!(get(&index, "def".chars()), vec![]);
    }

    /// The trie should return prefixes for entire words.
    /// For example "re" should match "retry".
    #[test]
    fn longer_needle_than_haystack() {
        let mut index: AffixIndex<usize> = Default::default();
        index.push("re".chars(), 1);

        assert_eq!(get(&index, "retry".chars()), vec![1]);
        assert_eq!(get(&index, "terminate".chars()), vec![]);
    }

    /// Check that even if we're looking up the same char at the
    /// same depth ('c' at depth 2 (zero-indexed) in this case),
    /// the lookup doesn't collide with any other entry which
    /// uses that same char at the same depth.
    #[test]
    fn depth_and_char_collision_test() {
        let mut index: AffixIndex<usize> = Default::default();
        index.push("abc".chars(), 123);
        index.push("bac".chars(), 213);

        assert_eq!(get(&index, "abc".chars()), vec![123]);
        assert_eq!(get(&index, "bac".chars()), vec![213]);
    }

    #[test]
    fn returns_values_from_multiple_entries() {
        let mut index: AffixIndex<usize> = Default::default();
        index.push("s".chars().rev(), 1);
        index.push("ions".chars().rev(), 2);
        index.push("ications".chars().rev(), 3);

        assert_eq!(get(&index, "s".chars().rev()), vec![1]);
        assert_eq!(get(&index, "ions".chars().rev()), vec![1, 2]);
        assert_eq!(get(&index, "ications".chars().rev()), vec![1, 2, 3]);
    }
}
