//! A lightweight, Hunspell-like spell checking library.

// TODO: remove.
#![allow(dead_code)]
#![no_std]

extern crate alloc;
use core::{cmp::Ordering, fmt, hash::BuildHasher};

use aff::AffData;
use alloc::{boxed::Box, slice, vec::Vec};

pub(crate) mod aff;
pub(crate) mod checker;
mod hash_multi_map;
pub(crate) mod macros;
pub(crate) mod stdx;

pub use aff::parser::{ParseDictionaryError, ParseDictionaryErrorKind, ParseDictionaryErrorSource};
use checker::Checker;

/// TODO
pub struct Dictionary<S: BuildHasher> {
    aff_data: AffData<S>,
}

impl<S: BuildHasher + Clone> Dictionary<S> {
    pub fn new_with_hasher(
        dic: &str,
        aff: &str,
        build_hasher: S,
    ) -> Result<Self, ParseDictionaryError> {
        let aff_data = aff::parser::parse(dic, aff, build_hasher)?;
        Ok(Self { aff_data })
    }
}

impl<S: BuildHasher + Clone + Default> Dictionary<S> {
    pub fn new(dic: &str, aff: &str) -> Result<Self, ParseDictionaryError> {
        Self::new_with_hasher(dic, aff, S::default())
    }
}

impl<S: BuildHasher> Dictionary<S> {
    pub fn check(&self, word: &str) -> bool {
        Checker::new(&self.aff_data).check(word)
    }

    // suggest(&self, word: &str) -> impl Iterator<Item = String> ?
    // accept a &mut Vec instead?
}

/// Compressed representation of a Flag.
///
/// Flags are used as attributes about words. For example a flag might mark a word as forbidden,
/// or it might prevent that word from being suggested. Words in a dictionary have sets of flags
/// associated to them that control which prefixes and suffixes apply to them.
///
/// For a simple example, consider a line in a dic file with the contents `drink/X`. "drink" has
/// just one flag: `X`. That `X` flag corresponds to a suffix rule in the en_US dictionary that
/// allows the "drink" _stem_ in the dictionary to be conjugated as full words like "drinkable."
///
/// Dictionaries declare a `FlagType` they will use to express flags. This `Flag` can represent
/// each of the four types.
///
/// * `FlagType::Short`: ASCII 8-bit characters are casted into 16 bits.
/// * `FlagType::Long`: the first ASCII character occupies the higher 8 bits and the second ASCII
///   character occupies the lower 8 bits.
/// * `FlagType::Numeric`: the flag is represented as a 16 bit integer.
/// * `FlagType::Utf8`: if the flag is fit into two bytes. Hunspell and Nuspell restrict UTF8
///   flags to UTF8 code-points representable in one or two bytes. Flags are just attributes, so
///   using symbols, emoji or non-latin alphabets is unnecessary. Languages like `ar` (Arabic)
///   use the `FlagType::Numeric` encoding for example.
///
/// Finally, a flag with a value of zero is not valid for any `FlagType`, so we can safely
/// represent this as a _non-zero_ u16. Hunspell calls this zero flag "`FLAG_NULL`". Layout
/// optimizations allow us to represent `Option<Flag>` in 16 bits.
///
/// Hunspell uses an `unsigned short` for flags while Nuspell uses a `char16_t`.
pub(crate) type Flag = core::num::NonZeroU16;

/// A collection of flags belonging to a word.
///
/// Nuspell represents this as a sorted `std::basic_string<char16_t>` (`char16_t` being the
/// representation) for flags. Hunspell uses a sorted `unsigned short*` and searches it via
/// `std::binary_search`.
///
/// We represent this in Spellbook with a sorted boxed slice of flags. We use a boxed slice to cut
/// down on the storage space required - a `Vec` has an extra capacity field that takes up some
/// extra bytes. Using a boxed slice reduces `size_of::<FlagSet>()` on my machine from 24 to 16.
/// This sounds insignificant but a dictionary might have very very many flagsets, so the savings
/// are potentially noticeable. Boxed slices also remove extra allocated capacity.
#[derive(Default, PartialEq, Eq, Clone)]
pub(crate) struct FlagSet {
    inner: Box<[Flag]>,
}

impl From<Vec<Flag>> for FlagSet {
    fn from(mut flags: Vec<Flag>) -> Self {
        flags.sort_unstable();
        flags.dedup();
        Self {
            inner: flags.into_boxed_slice(),
        }
    }
}

impl FlagSet {
    pub fn empty() -> Self {
        Self {
            inner: Box::new([]),
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[Flag] {
        &self.inner
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Flag> {
        self.inner.iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if both sets have at least one element in common.
    pub fn has_intersection(&self, other: &Self) -> bool {
        let mut xs = self.iter().peekable();
        let mut ys = other.iter().peekable();

        loop {
            match xs.peek().zip(ys.peek()) {
                Some((x, y)) => match x.cmp(y) {
                    Ordering::Equal => return true,
                    Ordering::Greater => {
                        ys.next();
                    }
                    Ordering::Less => {
                        xs.next();
                    }
                },
                _ => return false,
            }
        }
    }

    pub fn intersection(&self, other: &Self) -> Self {
        let mut intersection = Vec::new();
        let mut xs = self.iter().peekable();
        let mut ys = other.iter().peekable();

        while let Some((x, y)) = xs.peek().zip(ys.peek()) {
            match x.cmp(y) {
                Ordering::Equal => {
                    intersection.push(**x);
                    xs.next();
                    ys.next();
                }
                Ordering::Greater => {
                    ys.next();
                }
                Ordering::Less => {
                    xs.next();
                }
            }
        }

        Self {
            inner: intersection.into_boxed_slice(),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut union = Vec::new();
        let mut xs = self.iter().peekable();
        let mut ys = other.iter().peekable();

        loop {
            match (xs.peek(), ys.peek()) {
                (Some(x), Some(y)) => match x.cmp(y) {
                    Ordering::Equal => {
                        union.push(**x);
                        xs.next();
                        ys.next();
                    }
                    Ordering::Greater => {
                        union.push(**y);
                        ys.next();
                    }
                    Ordering::Less => {
                        union.push(**x);
                        xs.next();
                    }
                },
                (Some(_), None) => {
                    union.extend(xs.copied());
                    break;
                }
                (None, Some(_)) => {
                    union.extend(ys.copied());
                    break;
                }
                (None, None) => break,
            }
        }

        Self {
            inner: union.into_boxed_slice(),
        }
    }

    /// Checks whether the given flag is contained in the flagset.
    #[inline]
    pub fn contains(&self, flag: &Flag) -> bool {
        self.inner.binary_search(flag).is_ok()
    }
}

impl fmt::Debug for FlagSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("flagset!{:?}", self.inner))
    }
}

// We represent the stem as a boxed str to save on space.
pub(crate) type WordList<S> = hash_multi_map::HashMultiMap<Box<str>, FlagSet, S>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum AffixingMode {
    FullWord,
    AtCompoundBegin,
    AtCompoundMiddle,
    AtCompoundEnd,
}

impl Default for AffixingMode {
    fn default() -> Self {
        Self::FullWord
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn flagset_from_iter() {
        // Items are deduplicated and sorted.
        assert_eq!(
            &[flag!(1), flag!(2), flag!(3)],
            flagset![1, 3, 2, 1].as_slice()
        )
    }

    #[test]
    fn flagset_has_intersection() {
        assert!(flagset![1, 2, 3].has_intersection(&flagset![1]));
        assert!(flagset![1, 2, 3].has_intersection(&flagset![2]));
        assert!(flagset![1, 2, 3].has_intersection(&flagset![3]));
        assert!(flagset![2].has_intersection(&flagset![1, 2, 3]));

        assert!(!flagset![1, 2, 3].has_intersection(&flagset![4, 5, 6]));
        assert!(!flagset![4, 5, 6].has_intersection(&flagset![1, 2, 3]));

        assert!(!flagset![1, 3, 5].has_intersection(&flagset![2, 4, 6]));

        assert!(!flagset![].has_intersection(&flagset![]));
    }

    #[test]
    fn flagset_intersection() {
        assert_eq!(flagset![], flagset![].intersection(&flagset![]));
        assert_eq!(flagset![], flagset![1, 3].intersection(&flagset![2]));
        assert_eq!(flagset![], flagset![2].intersection(&flagset![1, 3]));
        assert_eq!(flagset![2], flagset![1, 2, 3].intersection(&flagset![2]));
        assert_eq!(
            flagset![1, 3],
            flagset![1, 2, 3].intersection(&flagset![1, 3])
        );
        assert_eq!(
            flagset![1, 2, 3],
            flagset![1, 2, 3].intersection(&flagset![1, 2, 3])
        );
    }

    #[test]
    fn flagset_union() {
        assert_eq!(flagset![], flagset![].union(&flagset![]));
        assert_eq!(flagset![1, 2, 3], flagset![1, 3].union(&flagset![2]));
        assert_eq!(flagset![1, 2, 3], flagset![2].union(&flagset![1, 3]));
        assert_eq!(
            flagset![1, 2, 3],
            flagset![1, 2, 3].union(&flagset![1, 2, 3])
        );
    }

    #[test]
    fn flagset_contains() {
        assert!(flagset![1, 2, 3].contains(&flag!(1)));
        assert!(flagset![1, 2, 3].contains(&flag!(2)));
        assert!(flagset![1, 2, 3].contains(&flag!(3)));
        assert!(!flagset![1, 2, 3].contains(&flag!(4)));
    }
}
