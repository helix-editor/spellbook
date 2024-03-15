//! A lightweight, Hunspell-like spell checking library.

// TODO: remove.
#![allow(dead_code)]
#![no_std]

extern crate alloc;
use core::{cmp::Ordering, fmt, hash::BuildHasher};

use alloc::{
    slice,
    string::String,
    vec::{self, Vec},
};

pub(crate) mod aff;
mod hash_multi_map;
pub(crate) mod macros;

/// TODO
pub struct Dictionary<S: BuildHasher> {
    aff_data: aff::AffData<S>,
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
        self.aff_data.words.get(word).is_some()
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
/// `std::binary_search`. We represent this in Spellbook with a sorted `Vec`.
#[derive(Default, PartialEq, Eq, Clone)]
pub(crate) struct FlagSet {
    inner: Vec<Flag>,
}

impl FromIterator<Flag> for FlagSet {
    fn from_iter<T: IntoIterator<Item = Flag>>(iter: T) -> Self {
        let mut inner: Vec<_> = iter.into_iter().collect();
        inner.sort_unstable();
        inner.dedup();
        Self { inner }
    }
}

impl FlagSet {
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Flag> {
        self.inner.iter()
    }

    #[inline]
    pub fn into_iter(self) -> vec::IntoIter<Flag> {
        self.inner.into_iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn insert(&mut self, flag: Flag) {
        let partition = self.inner.partition_point(|&f| f < flag);
        self.inner.insert(partition, flag);
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
            inner: intersection,
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

        Self { inner: union }
    }

    // TODO: better name.
    pub fn merge(&mut self, other: &Self) {
        self.inner.extend(other.iter().copied());
        self.inner.sort_unstable();
        self.inner.dedup();
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

pub(crate) type WordList<S> = hash_multi_map::HashMultiMap<String, FlagSet, S>;

#[derive(Debug)]
pub struct ParseDictionaryError {
    pub kind: ParseDictionaryErrorKind,
    pub source: ParseDictionaryErrorSource,
    pub line_number: Option<usize>,
}

impl fmt::Display for ParseDictionaryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line_number {
            Some(line) => write!(
                f,
                "failed to parse {} file on line {}: {}",
                self.source, line, self.kind
            ),
            None => write!(f, "failed to parse {} file: {}", self.source, self.kind),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ParseDictionaryErrorSource {
    Dic,
    Aff,
    // Personal, ?
}

impl fmt::Display for ParseDictionaryErrorSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dic => write!(f, ".dic"),
            Self::Aff => write!(f, ".aff"),
        }
    }
}

#[derive(Debug)]
pub enum ParseDictionaryErrorKind {
    UnknownFlagType(aff::UnknownFlagTypeError),
    MalformedFlag(aff::ParseFlagError),
    MalformedNumber(core::num::ParseIntError),
    UnexpectedNonWhitespace(char),
    MismatchedArity { expected: usize, actual: usize },
    MismatchedRowCount { expected: usize, actual: usize },
    // MalformedCompoundRule(ParseCompoundRuleError),
    // MalformedMorphologicalField(String),
    MalformedAffix,
    MalformedCondition(aff::ConditionError),
    Empty,
}

impl From<aff::UnknownFlagTypeError> for ParseDictionaryErrorKind {
    fn from(err: aff::UnknownFlagTypeError) -> Self {
        Self::UnknownFlagType(err)
    }
}

impl From<aff::ParseFlagError> for ParseDictionaryErrorKind {
    fn from(err: aff::ParseFlagError) -> Self {
        Self::MalformedFlag(err)
    }
}

impl From<aff::ConditionError> for ParseDictionaryErrorKind {
    fn from(err: aff::ConditionError) -> Self {
        Self::MalformedCondition(err)
    }
}

impl fmt::Display for ParseDictionaryErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownFlagType(err) => err.fmt(f),
            Self::MalformedFlag(err) => {
                write!(f, "flag is malformed: {}", err)
            }
            Self::MalformedNumber(err) => err.fmt(f),
            Self::UnexpectedNonWhitespace(ch) => {
                write!(f, "unexpected non-whitespace character '{}'", ch)
            }
            Self::MismatchedArity { expected, actual } => {
                write!(f, "expected {} arguments but found {}", expected, actual)
            }
            Self::MismatchedRowCount { expected, actual } => {
                write!(f, "expected {} rows but found {}", expected, actual)
            }
            // Self::MalformedCompoundRule(err) => {
            //     write!(f, "compound rule is malformed: {}", err)
            // }
            // Self::MalformedMorphologicalField(s) => {
            //     write!(f, "morphological field '{}' is malformed", s)
            // }
            Self::MalformedAffix => write!(f, "failed to parse affix"),
            Self::MalformedCondition(err) => write!(f, "condition is malformed: {}", err),
            Self::Empty => write!(f, "the file is empty"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::alloc::vec;

    #[test]
    fn flagset_from_iter() {
        // Items are deduplicated and sorted.
        assert_eq!(
            vec![1, 2, 3],
            flagset![1, 3, 2, 1]
                .iter()
                .map(|flag| flag.get())
                .collect::<Vec<_>>()
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
