//! A spellchecking library compatible with the Hunspell dictionary format.
//!
//! Spellbook is a lightweight library to do spellchecking based on Hunspell dictionaries. It's
//! essentially a rewrite of the excellent C++ library [Nuspell] in Rust. Spellbook is `no_std`
//! (but requires alloc) and carries only [`hashbrown`] as a dependency.
//!
//! ```
//! let aff = std::fs::read_to_string("./vendor/en_US/en_US.aff").unwrap();
//! let dic = std::fs::read_to_string("./vendor/en_US/en_US.dic").unwrap();
//! let dict = spellbook::Dictionary::new(&aff, &dic).unwrap();
//!
//! assert!(dict.check("hello"));
//! assert!(dict.check("world"));
//! assert!(!dict.check("foobarbaz"));
//! ```
//!
//! [Nuspell]: https://github.com/nuspell/nuspell
//! [`hashbrown`]: https://github.com/rust-lang/hashbrown
// TODO: more.

// TODO: remove.
#![allow(dead_code)]
#![no_std]

extern crate alloc;

pub(crate) mod aff;
pub(crate) mod checker;
mod hash_bag;

pub use aff::parser::{
    ParseDictionaryError, ParseDictionaryErrorKind, ParseDictionaryErrorSource, ParseFlagError,
};

use crate::alloc::{borrow::Cow, boxed::Box, slice, string::String, vec::Vec};
use aff::AffData;
use checker::Checker;
use core::{cmp::Ordering, fmt, hash::BuildHasher};
use hash_bag::HashBag;

/// Default hasher for hash tables.
///
/// This type is only meaningful if the `default-hasher` feature is enabled. This type isn't meant
/// to be used directly: it's used internally to provide a default hasher for [`Dictionary::new`].
#[cfg(feature = "default-hasher")]
pub type DefaultHashBuilder = core::hash::BuildHasherDefault<ahash::AHasher>;

/// Dummy default hasher for hash tables.
///
/// This type is empty and useless unless the `default-hasher` feature is enabled. Instead of
/// using this type you should pass your chosen hasher into [`Dictionary::new_with_hasher`].
#[cfg(not(feature = "default-hasher"))]
pub enum DefaultHashBuilder {}

/// A collection of stems and their associated flagsets from a dictionary's `.dic` file.
///
/// This is like a `HashMap<String, FlagSet>` but we use a `Box<str>` to save on space and we
/// allow multiple entries of the same stem string. See the `HashBag` type for a more detailed
/// description.
pub(crate) type WordList<S> = HashBag<Box<str>, FlagSet, S>;

/// A data structure allowing for fast lookup of words in a dictionary.
///
/// Spellbook reads dictionaries in the Hunspell format: a pair of files `<locale>.aff` describing
/// rules for checking and suggesting words and `<locale>.dic` containing a listing of stems and
/// flags that describe words in the dictionary. You can find dictionaries for your locale in the
/// [LibreOffice/dictionaries](https://github.com/LibreOffice/dictionaries) repository.
///
/// To check whether a word is spelled correctly use [`check`]. Also see [`add`] to insert words
/// into an existing dictionary - this can be useful for building a "personal dictionary" feature.
///
/// ## Performance
///
/// Note: Spellbook's repository contains benchmarking examples. Use `cargo run --release
/// --example bench-api` to get an idea of how the API can perform on your system.
///
/// When using Spellbook in an application you should avoid initializing dictionaries (via
/// [`new`] or [`new_with_hasher`]) in a render loop or main thread to prevent pauses in your UI
/// if possible. Using a release build, dictionary initialization can take on the order of tens or
/// hundreds of milliseconds depending on the size of the input dictionary.
///
/// The [`check`] function is very fast: in the best case a word can be checked in around 50ns. In
/// the worst case a word might take on the order of single-digit microseconds, so throughput for
/// checking words should be expected to be somewhere in the millions of words per second. (This
/// is just checking though, note that tokenization of input will add overhead.) This might be
/// fast enough to live in a render loop or main thread but consider the size of your input: if
/// you're checking an arbitrarily large text you should delegate checking to a background thread
/// to prevent UI hiccups.
///
/// <!-- TODO: talk about suggest once implemented. Suggest performance is not so crucial. -->
///
/// You should avoid cloning this type if possible. `Clone` is only implemented in case you
/// absolutely need it. Consider that a dictionary can take megabytes of memory. If you need to
/// check words in parallel, consider putting the dictionary behind an `Arc` (if immutable) or a
/// `RwLock`.
///
/// [`new`]: struct.Dictionary.html#method.new
/// [`new_with_hasher`]: struct.Dictionary.html#method.new_with_hasher
/// [`check`]: struct.Dictionary.html#method.check
/// [`add`]: struct.Dictionary.html#method.add
// TODO: impl a dumb Debug for Dictionary.
// Allow passing down an Allocator too?
#[derive(Clone)]
pub struct Dictionary<S = DefaultHashBuilder> {
    words: WordList<S>,
    aff_data: AffData,
}

#[cfg(feature = "default-hasher")]
impl Dictionary<DefaultHashBuilder> {
    /// Initializes a new dictionary with the default hasher.
    ///
    /// This function is only available if the `default-hasher` feature is enabled (true by
    /// default). If the `default-hasher` feature is disabled then you must use
    /// [`new_with_hasher`] instead and provide a build hasher.
    ///
    /// [`new_with_hasher`]: struct.Dictionary.html#method.new_with_hasher
    ///
    /// # Example
    ///
    /// ```
    /// let aff = std::fs::read_to_string("./vendor/en_US/en_US.aff").unwrap();
    /// let dic = std::fs::read_to_string("./vendor/en_US/en_US.dic").unwrap();
    /// let dict = spellbook::Dictionary::new(&aff, &dic).unwrap();
    /// ```
    // TODO: what to accept other than `&str`? Would this play well with the Read trait? An
    // iterator over lines?
    pub fn new(aff: &str, dic: &str) -> Result<Self, ParseDictionaryError> {
        Self::new_with_hasher(aff, dic, DefaultHashBuilder::default())
    }
}

impl<S: BuildHasher + Clone> Dictionary<S> {
    /// Initializes a new dictionary with a custom `BuildHasher`.
    ///
    /// While the `default-hasher` feature is enabled, passing [`DefaultHashBuilder`] is the same
    /// as calling [`new`]. If possible, using a non-cryptographic hasher is highly recommended
    /// for the sake of performance.
    ///
    /// [`new`]: struct.Dictionary.html#method.new
    ///
    /// # Example
    ///
    /// ```
    /// let aff = std::fs::read_to_string("./vendor/en_US/en_US.aff").unwrap();
    /// let dic = std::fs::read_to_string("./vendor/en_US/en_US.dic").unwrap();
    /// let hasher = ahash::RandomState::new();
    /// let dict = spellbook::Dictionary::new_with_hasher(&aff, &dic, hasher).unwrap();
    /// ```
    pub fn new_with_hasher(
        aff: &str,
        dic: &str,
        build_hasher: S,
    ) -> Result<Self, ParseDictionaryError> {
        let (words, aff_data) = aff::parser::parse(aff, dic, build_hasher)?;
        Ok(Self { words, aff_data })
    }
}

impl<S: BuildHasher> Dictionary<S> {
    /// Checks whether the given word is in the dictionary.
    ///
    /// Spellbook delegates tokenization of input to the caller: `check` does not attempt to
    /// break up prose, punctuation or programming languages. Some dictionaries define "break
    /// patterns" which Spellbook respects though. For example `check("light-weight-like")`
    /// returns `true` for the `en_US` dictionary because the break patterns allow splitting into
    /// the words "light", "weight" and "like".
    ///
    /// # Example
    ///
    /// ```
    /// let aff = std::fs::read_to_string("./vendor/en_US/en_US.aff").unwrap();
    /// let dic = std::fs::read_to_string("./vendor/en_US/en_US.dic").unwrap();
    /// let dict = spellbook::Dictionary::new(&aff, &dic).unwrap();
    ///
    /// assert!(dict.check("optimize"));
    /// assert!(!dict.check("optimise")); // allowed by en_GB but not en_US.
    /// ```
    pub fn check(&self, word: &str) -> bool {
        Checker::new(self).check(word)
    }

    // suggest(&self, word: &str) -> impl Iterator<Item = String> ?
    // accept a &mut Vec instead?

    /// Adds a word to the dictionary.
    ///
    /// This function parses the input string the same way that Spellbook parses a line from a
    /// dictionary's `.dic` file. <!-- TODO: description of dic line parsing -->
    ///
    /// This function can be used to support for "personal" dictionaries. While clicking a
    /// misspelled word you might present a user with an option to add a misspelled word to the
    /// dictionary. That action might add the word to an append-only "personal-dictionary" text
    /// file and call this function. Then on restarting/reloading the application, you can `add`
    /// all lines in the file.
    ///
    /// # Example
    ///
    /// ```
    /// let aff = std::fs::read_to_string("./vendor/en_US/en_US.aff").unwrap();
    /// let dic = std::fs::read_to_string("./vendor/en_US/en_US.dic").unwrap();
    /// let mut dict = spellbook::Dictionary::new(&aff, &dic).unwrap();
    ///
    /// assert!(!dict.check("foobarbaz"));
    /// // In the `en_US` dictionary the 'G' suffix allows "ing" at the end of the word.
    /// dict.add("foobarbaz/G").unwrap();
    /// assert!(dict.check("foobarbaz"));
    /// assert!(dict.check("foobarbazing"));
    ///
    /// // Adding to a dictionary might fail if the line cannot be parsed. For example, a flag
    /// // using a UTF-8 character that takes more than two bytes is not allowed.
    /// assert_eq!("😓".len(), 4); // 😓 is 4 bytes in UTF-8: 0xf0 0x9f 0x98 0x93
    /// assert!(dict.add("notallowed/😓").is_err());
    /// ```
    pub fn add(&mut self, input: &str) -> Result<(), ParseFlagError> {
        // This impl might be expanded in the future.
        // Can we do some clever storage in compound rules that lists the bytes/chars that might
        // start a compound (created by compound rules)? Then we might need to update that info
        // here as well as during `new`.
        // TODO: for the sake of personal dictionaries consider adding an `extend` function which
        // takes an iterator of `.dic` file lines, uses the size hint to preallocate and only
        // appends any word if all words succeed in parsing.
        let (word, flagset) = aff::parser::parse_dic_line(
            input,
            self.aff_data.flag_type,
            &self.aff_data.flag_aliases,
            &self.aff_data.ignore_chars,
        )?;
        self.words.insert(word, flagset);
        Ok(())
    }
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
/// * `FlagType::Short`: ASCII 8-bit characters are cast into 16 bits.
/// * `FlagType::Long`: the first ASCII character occupies the higher 8 bits and the second ASCII
///   character occupies the lower 8 bits.
/// * `FlagType::Numeric`: the flag is represented as a 16 bit integer.
/// * `FlagType::Utf8`: the flag is fit into two bytes if possible. Hunspell and Nuspell restrict
///   UTF8 flags to UTF8 code-points representable in one or two bytes. Flags are just attributes,
///   so using symbols, emoji or non-Latin alphabets is unnecessary. Languages like `ar` (Arabic)
///   use the `FlagType::Numeric` encoding for example.
///
/// Finally, a flag with a value of zero is not valid for any `FlagType`, so we can safely
/// represent this as a _non-zero_ u16. Hunspell calls this zero flag "`FLAG_NULL`". Layout
/// optimizations allow us to represent `Option<Flag>` in 16 bits.
///
/// Hunspell uses an `unsigned short` for flags while Nuspell uses a `char16_t`.
// TODO: experiment with using a regular u16 instead. Because the flags are not defined as zero
// in `.aff` files, we can use regular u16 comparison to check if a flag is set rather than
// checking an option. For example what we do now is basically
// `flag.is_some_and(|flag| flagset.contains(flag))` but could be simply `flagset.contains(flag)`,
// and we could optionally also modify `FlagSet::contains` to bail early if it sees 0u16.
pub(crate) type Flag = core::num::NonZeroU16;

/// A collection of flags belonging to a word.
///
/// Nuspell represents this as a sorted `std::basic_string<char16_t>` (`char16_t` being the
/// representation for flags). Hunspell uses a sorted `unsigned short*` and searches it via
/// `std::binary_search`.
///
/// We represent this in Spellbook with a sorted boxed slice of flags. We use a boxed slice to cut
/// down on the storage space required - a `Vec` has an extra capacity field that takes up some
/// extra bytes. Using a boxed slice reduces `size_of::<FlagSet>()` on my machine from 24 to 16.
/// This sounds insignificant but a dictionary might have very very many flagsets, so the savings
/// are potentially noticeable. Boxed slices also remove extra allocated capacity. Generally
/// there's no need to use a Vec, String or other similar owned types over a boxed equivalent
/// unless the value needs to be mutated at some point. Once a dictionary is initialized it's
/// immutable so we don't need a Vec.
#[derive(Default, PartialEq, Eq, Clone)]
pub(crate) struct FlagSet(Box<[Flag]>);

impl From<Vec<Flag>> for FlagSet {
    fn from(mut flags: Vec<Flag>) -> Self {
        flags.sort_unstable();
        flags.dedup();
        Self(flags.into_boxed_slice())
    }
}

impl FlagSet {
    pub fn empty() -> Self {
        Self::default()
    }

    #[inline]
    pub fn as_slice(&self) -> &[Flag] {
        &self.0
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Flag> {
        self.0.iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
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

        Self(intersection.into_boxed_slice())
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

        Self(union.into_boxed_slice())
    }

    /// Checks whether the given flag is contained in the flagset.
    #[inline]
    pub fn contains(&self, flag: &Flag) -> bool {
        // See the docs for `slice::binary_search`: it's preferable to `slice::contains` since
        // it runs in logarithmic time rather than linear w.r.t. slice length. It requires that
        // the slice is sorted (true for flagsets, see `new`).
        self.0.binary_search(flag).is_ok()
    }

    pub fn with_flag(&self, flag: Flag) -> Self {
        let mut flagset = Vec::from(self.0.clone());
        flagset.push(flag);
        flagset.into()
    }
}

impl fmt::Debug for FlagSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("flagset!{:?}", self.0))
    }
}

// Ideally these would be an enum but const generics do not yet support custom enums.
pub(crate) type AffixingMode = u8;
pub(crate) const FULL_WORD: AffixingMode = 0;
pub(crate) const AT_COMPOUND_BEGIN: AffixingMode = 1;
pub(crate) const AT_COMPOUND_MIDDLE: AffixingMode = 2;
pub(crate) const AT_COMPOUND_END: AffixingMode = 3;

/// The casing of a word.
// Hunspell: <https://github.com/hunspell/hunspell/blob/8f9bb2957bfd74ca153fad96083a54488b518ca5/src/hunspell/csutil.hxx#L91-L96>
// Nuspell: <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/src/nuspell/utils.hxx#L91-L104>
pub(crate) enum Casing {
    /// All letters are lowercase. For example "foobar".
    ///
    /// Hunspell: `NOCAP`, Nuspell: `Casing::SMALL`
    None,
    /// First letter is capitalized only. For example "Foobar".
    ///
    /// Hunspell: `INITCAP`, Nuspell: `Casing::INIT_CAPITAL`
    Init,
    /// All letters are capitalized. For example "FOOBAR".
    ///
    /// Hunspell: `ALLCAP`, Nuspell: `Casing::ALL_CAPITAL`
    All,
    /// Some but not all letters are capitalized. The first letter is not capitalizated.
    /// For example "fooBar".
    ///
    /// Hunspell: `HUHCAP`, Nuspell: `Casing::CAMEL`
    Camel,
    /// Some but not all letters are capitalized. The first letter is capitalized.
    /// For example "FooBar".
    ///
    /// Hunspell: `HUHINITCAP`, Nuspell: `Casing::PASCAL`
    Pascal,
}

pub(crate) fn classify_casing(word: &str) -> Casing {
    let mut upper = 0;
    let mut lower = 0;

    for ch in word.chars() {
        if ch.is_uppercase() {
            upper += 1;
        }
        if ch.is_lowercase() {
            lower += 1;
        }
    }

    if upper == 0 {
        return Casing::None;
    }

    // SAFETY: `word.chars()` has at least one element or we would have returned above.
    let first_capital = word.chars().next().unwrap().is_uppercase();

    if first_capital && upper == 1 {
        Casing::Init
    } else if lower == 0 {
        Casing::All
    } else if first_capital {
        Casing::Pascal
    } else {
        Casing::Camel
    }
}

pub(crate) fn erase_chars<'a>(word: &'a str, ignore: &[char]) -> Cow<'a, str> {
    if ignore.is_empty() {
        Cow::Borrowed(word)
    } else {
        Cow::Owned(
            word.chars()
                .filter(|ch| !ignore.contains(ch))
                .collect::<String>(),
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
    const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");
    // static EN_US: Lazy<Dictionary> = Lazy::new(|| Dictionary::new(EN_US_AFF, EN_US_DIC).unwrap());

    macro_rules! flag {
        ( $x:expr ) => {{
            Flag::new($x as u16).unwrap()
        }};
    }
    macro_rules! flagset {
        () => {{
            FlagSet::empty()
        }};
        ( $( $x:expr ),* ) => {
            {
                FlagSet::from( $crate::alloc::vec![ $( Flag::new( $x as u16 ).unwrap() ),* ] )
            }
        };
    }

    #[test]
    fn flagset_display() {
        assert_eq!("flagset![1]", &alloc::format!("{:?}", flagset![1]));
    }

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

    #[test]
    fn classify_casing_nuspell_unit_test() {
        // Upstream: <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/tests/unit_test.cxx#L451-L459>

        assert!(matches!(classify_casing(""), Casing::None));
        assert!(matches!(classify_casing("здраво"), Casing::None));
        assert!(matches!(classify_casing("Здраво"), Casing::Init));
        assert!(matches!(classify_casing("ЗДРАВО"), Casing::All));
        assert!(matches!(classify_casing("здРаВо"), Casing::Camel));
        assert!(matches!(classify_casing("ЗдрАво"), Casing::Pascal));
    }

    #[test]
    fn erase_chars_test() {
        fn erase_chars(word: &str, ignore: &[char]) -> String {
            super::erase_chars(word, ignore).into_owned()
        }
        assert_eq!(
            erase_chars("example", &['a', 'e', 'i', 'o', 'u']),
            String::from("xmpl")
        );
    }

    #[test]
    fn new_on_bad_dictionary() {
        let aff = r#"
        FLAG num
        "#;
        // Not numeric flags:
        let dic = r#"1
        hello/world
        "#;
        assert!(Dictionary::new(aff, dic).is_err());
    }

    #[test]
    fn add_word() {
        let mut dict = Dictionary::new(EN_US_AFF, EN_US_DIC).unwrap();
        assert!(!dict.check("foobarbaz"));
        dict.add("foobarbaz/G").unwrap();
        assert!(dict.check("foobarbaz"));
        assert!(dict.check("foobarbazing"));

        assert!(dict.add("notallowed/😓").is_err());
    }

    #[test]
    fn clone() {
        let aff = r#"
        "#;
        let dic = r#"1
        hello
        world
        "#;
        let mut dict = Dictionary::new(aff, dic).unwrap();
        let copy = dict.clone();
        dict.add("foo").unwrap();
        assert!(dict.check("foo"));
        assert!(!copy.check("foo"));
    }
}
