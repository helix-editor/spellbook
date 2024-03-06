//! A lightweight, Hunspell-like spell checking library.

// TODO: remove.
#![allow(dead_code)]
#![no_std]

extern crate alloc;
use alloc::vec::Vec;

pub(crate) mod aff;

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
#[derive(Default)]
pub(crate) struct FlagSet {
    inner: Vec<Flag>,
}

impl FlagSet {
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn from_iter<I: Iterator<Item = Flag>>(iter: I) -> Self {
        let mut inner: Vec<_> = iter.collect();
        inner.sort_unstable();
        inner.dedup();
        Self { inner }
    }
}
