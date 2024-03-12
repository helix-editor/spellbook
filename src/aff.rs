use hashbrown::raw::{RawIterHash, RawTable};

use crate::{
    alloc::{
        borrow::Cow,
        string::{String, ToString},
        vec::Vec,
    },
    Flag, FlagSet,
};

use core::{
    hash::{BuildHasher, Hash, Hasher},
    marker::PhantomData,
    str::Chars,
};

/// The representation of a flag in a `.dic` or `.aff` file.
///
/// This representation also decides how we encode flags into `Flag`. This is controlled by the
/// `FLAG` directive in a `.aff` file.
#[derive(Debug, Clone, Copy)]
pub(crate) enum FlagType {
    /// A single ascii character.
    ///
    /// This is the default representation if a `.aff` file does not specify another.
    Short,
    /// Two adjacent ascii characters.
    ///
    /// The french dictionary uses this. For example for some proper nouns like `Asimov/L'D'Q'`,
    /// `L'` is a flag, `D'` another, `Q'` another.
    Long,
    /// A number in the range `1..=65000`.
    ///
    /// We will approximate this to `2^16`. Numeric flags are separated by commas.
    /// For example `actionfilm/70,7,252,976` from the Danish dictionary.
    Numeric,
    /// One UTF8 character described by at most two bytes.
    Utf8,
}

impl Default for FlagType {
    fn default() -> Self {
        Self::Short
    }
}

#[derive(Debug, Clone)]
pub struct UnknownFlagTypeError(String);

impl core::str::FromStr for FlagType {
    type Err = UnknownFlagTypeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "long" => Ok(Self::Long),
            "num" => Ok(Self::Numeric),
            "UTF-8" => Ok(Self::Utf8),
            _ => Err(UnknownFlagTypeError(s.to_string())),
        }
    }
}

impl core::fmt::Display for UnknownFlagTypeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "expected FLAG to be `long`, `num` or `UTF-8` if set, found {}",
            self.0
        )
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Condition {
    /// The input pattern.
    ///
    /// The condition string is not transformed or compiled into a different input. We'll iterate
    /// over it directly to attempt to match the pattern.
    ///
    /// This string is non-empty.
    pattern: String,
    /// The number of `char`s that the pattern describes.
    ///
    /// `Condition` is such a small subset of regex that we can tell only from a linear scan of
    /// the input how many characters we will attempt to match.
    chars: usize,
}

impl Condition {
    pub fn matches(&self, input: &str) -> bool {
        let mut input = input.chars().peekable();
        let mut pattern = self.pattern.chars().peekable();

        loop {
            match (pattern.next(), input.next()) {
                // If we're at the end of both inputs, this is a match.
                (None, None) => return true,
                // Inputs of different lengths are not a match.
                (Some(_), None) | (None, Some(_)) => return false,
                // Wildcard: skip the input character.
                (Some('.'), Some(_)) => (),
                // Character classes
                (Some('['), Some(input_ch)) => {
                    let mut found = false;
                    let negative = pattern.next_if_eq(&'^').is_some();

                    for ch in pattern.by_ref() {
                        if ch == ']' {
                            break;
                        }

                        if ch == input_ch {
                            found = true;
                        }
                    }

                    // If it's a positive character class and the character isn't a member,
                    // this is not a match.
                    if !negative && !found {
                        return false;
                    }
                    // If it's a negative character class and the character _is_ a member,
                    // this is not a match.
                    if negative && found {
                        return false;
                    }
                }
                // Literals: the pattern character must equal the input character.
                (Some(pattern_ch), Some(input_ch)) => {
                    if pattern_ch != input_ch {
                        return false;
                    }
                }
            }
        }
    }
}

/// An error arising from validating a [`Condition`].
///
/// Conditions are a subset of regular expressions that include positive and negative character
/// classes and the wildcard character. A condition might fail validation if the character classes
/// are open (for example `foo]` or `foo[bar`) or if the condition has an empty character class,
/// which is not valid (`[]`).
// Hands where I can see 'em, clippy. The only time I ever went down was when a machine was easing
// at the wrong time.
#[allow(clippy::enum_variant_names)]
#[derive(Debug, PartialEq, Eq)]
pub enum ConditionError {
    /// The pattern contained an opening `[` character which did not match a closing `]`
    /// character.
    UnopenedCharacterClass,
    /// The pattern contained a closing `]` character which did not match an opening `[`
    /// character.
    UnclosedCharacterClass,
    /// The pattern contained the literal `[]` which is not a valid character class.
    EmptyCharacterClass,
}

impl core::fmt::Display for ConditionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnopenedCharacterClass => {
                f.write_str("closing bracket has no matching opening bracket")
            }
            Self::UnclosedCharacterClass => {
                f.write_str("opening bracket has no matching closing bracket")
            }
            Self::EmptyCharacterClass => f.write_str("empty bracket expression"),
        }
    }
}

impl core::str::FromStr for Condition {
    type Err = ConditionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // TODO when parsing: treat `"."` as `None`.
        let mut scan = s;
        let mut chars = 0;

        // Loop through the characters. We can't just iterate through the `.chars()` because we'll
        // be jumping ahead with the help of `find`.
        loop {
            // Find a bracket. Brackets signal character classes.
            let bracket_index = match scan.find(['[', ']']) {
                Some(index) => index,
                None => {
                    // If there isn't one, accept the rest of the string.
                    chars += scan.chars().count();
                    break;
                }
            };
            // If there is one, scan ahead to it.
            chars += scan[..bracket_index].chars().count();
            scan = &scan[bracket_index..];
            match scan
                .chars()
                .next()
                .expect("scan can't be empty if the pattern matched")
            {
                ']' => return Err(Self::Err::UnopenedCharacterClass),
                '[' => {
                    scan = &scan[1..];
                    match scan.chars().next() {
                        None => return Err(Self::Err::UnclosedCharacterClass),
                        Some('^') => scan = &scan[1..],
                        _ => (),
                    }

                    match scan.find(']') {
                        None => return Err(Self::Err::UnclosedCharacterClass),
                        Some(0) => return Err(Self::Err::EmptyCharacterClass),
                        Some(bracket_index) => {
                            // Only count the character class as one character.
                            chars += 1;
                            scan = &scan[bracket_index + 1..];
                            continue;
                        }
                    }
                }
                // This is impossible if find `find` found `[` or `]`.
                _ => unreachable!(),
            }
        }

        Ok(Self {
            pattern: String::from(s),
            chars,
        })
    }
}

/// Internal container type for a prefix or suffix.
pub(crate) struct Affix<K> {
    /// The flag that words may use to reference this affix.
    pub flag: Flag,
    /// Whether the affix is compatible with the opposite affix.
    /// For example a word that has both a prefix and a suffix, both the prefix
    /// and suffix should have `crossproduct: true`.
    pub crossproduct: bool,
    /// What is stripped from the stem when the affix is applied.
    pub strip: String,
    /// What should be added when the affix is applied.
    pub add: String,
    /// Condition that the stem should be checked against to query if the
    /// affix is relevant.
    condition: Option<Condition>,
    /// Flags the affix has itself.
    pub flags: FlagSet,
    phantom_data: PhantomData<K>,
}
impl<K> Affix<K> {
    pub fn new(
        flag: Flag,
        crossproduct: bool,
        strip: &str,
        add: String,
        condition: Option<&str>,
        flags: FlagSet,
    ) -> Result<Self, ConditionError> {
        let condition = condition.map(str::parse).transpose()?;

        Ok(Self {
            flag,
            crossproduct,
            strip: strip.to_string(),
            add,
            flags,
            condition,
            phantom_data: PhantomData,
        })
    }
}

#[derive(Debug)]
pub(crate) struct Pfx;
#[derive(Debug)]
pub(crate) struct Sfx;

/// Rules for replacing characters at the beginning of a stem.
pub(crate) type Prefix = Affix<Pfx>;
/// Rules for replacing characters at the end of a stem.
pub(crate) type Suffix = Affix<Sfx>;

pub(crate) trait AffixKind<'a> {
    type Chars: Iterator<Item = char>;

    fn chars(word: &'a str) -> Self::Chars;
}

impl<'a> AffixKind<'a> for Pfx {
    type Chars = Chars<'a>;

    fn chars(word: &'a str) -> Self::Chars {
        word.chars()
    }
}

impl<'a> AffixKind<'a> for Sfx {
    type Chars = core::iter::Rev<Chars<'a>>;

    fn chars(word: &'a str) -> Self::Chars {
        word.chars().rev()
    }
}

impl Prefix {
    /// Remove the `add` and add the `strip`
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        if word.starts_with(&self.add) {
            let mut stem = self.strip.clone();
            stem.push_str(&word[self.add.len()..]);
            Cow::Owned(stem)
        } else {
            Cow::Borrowed(word)
        }
    }

    pub fn condition_matches(&self, word: &str) -> bool {
        let condition = match &self.condition {
            Some(condition) => condition,
            None => return true,
        };

        // Length in bytes is greater than or equal to length in chars.
        if word.len() < condition.chars {
            return false;
        }

        condition.matches(word)
    }
}

impl Suffix {
    /// Remove the `add` and add the `strip`
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        if word.ends_with(&self.add) {
            let mut stem = word[..(word.len() - self.add.len())].to_string();
            stem.push_str(&self.strip);
            Cow::Owned(stem)
        } else {
            Cow::Borrowed(word)
        }
    }

    pub fn condition_matches(&self, word: &str) -> bool {
        let condition = match &self.condition {
            Some(condition) => condition,
            None => return true,
        };

        // Length in bytes is greater than or equal to length in chars.
        if word.len() < condition.chars {
            return false;
        }

        let buffer = &mut [0; 4];
        let (chars, bytes) =
            word.chars()
                .rev()
                .take(condition.chars)
                .fold((0, 0), |(chars, bytes), ch| {
                    // TODO: convert to a u32 instead and check with bit math how many bytes
                    // the code point takes.
                    (chars + 1, bytes + ch.encode_utf8(buffer).len())
                });

        if chars < condition.chars {
            return false;
        }
        condition.matches(&word[word.len() - bytes..])
    }
}

pub(crate) struct AffixIndex<K, S: BuildHasher> {
    empty: Vec<Affix<K>>,
    table: RawTable<Affix<K>>,
    build_hasher: S,
    all_continuation_flags: FlagSet,
}

impl<'a, K, S> AffixIndex<K, S>
where
    K: AffixKind<'a>,
    S: BuildHasher,
{
    pub fn insert(&mut self, affix: Affix<K>) {
        self.all_continuation_flags.merge(&affix.flags);
        if affix.add.is_empty() {
            self.empty.push(affix);
        } else {
            let build_hasher = &self.build_hasher;
            let hasher = move |affix: &Affix<K>| {
                let mut state = build_hasher.build_hasher();
                // TODO: something is very wrong about the AffixKind trait here.
                let add = unsafe { core::mem::transmute::<&str, &'static str>(&affix.add) };
                for ch in K::chars(add) {
                    ch.hash(&mut state);
                }
                state.finish()
            };
            let hash = hasher(&affix);
            self.table.insert(hash, affix, hasher);
        }
    }

    /// Returns all affixes that match the search word.
    ///
    /// An affix matches the search word if its `add` field is a prefix of the search word (when
    /// looking up prefixes) or a suffix of the search word (when looking up suffixes).
    pub fn find(&'a self, search_word: &'a str) -> FindAffixesIter<'a, K, S::Hasher> {
        FindAffixesIter {
            empty: self.empty.iter(),
            table: &self.table,
            table_iter: None,
            chars: K::chars(search_word),
            hasher: self.build_hasher.build_hasher(),
            visited_chars: Vec::new(),
        }
    }
}

pub(crate) struct FindAffixesIter<'a, K: AffixKind<'a>, H: Hasher> {
    empty: core::slice::Iter<'a, Affix<K>>,
    table: &'a RawTable<Affix<K>>,
    table_iter: Option<RawIterHash<Affix<K>>>,
    chars: K::Chars,
    hasher: H,
    visited_chars: Vec<char>,
}

impl<'a, K: AffixKind<'a>, H: Hasher> Iterator for FindAffixesIter<'a, K, H> {
    type Item = &'a Affix<K>;

    fn next(&mut self) -> Option<Self::Item> {
        // All empty affixes apply. Emit those first.
        if let Some(next_empty) = self.empty.next() {
            return Some(next_empty);
        }

        // Once we're out of empty affixes, lookup affixes with matching `add`s via the radix
        // tree.
        loop {
            // If we have a search for the current input character, return all affixes matching
            // the substring.
            if let Some(mut iter) = self.table_iter.take() {
                while let Some(next) = iter.next() {
                    // SAFETY: the lifetime of the returned value is bound to the table.
                    let affix = unsafe { next.as_ref() };

                    if K::chars(&affix.add)
                        .zip(self.visited_chars.iter())
                        .all(|(ach, vch)| ach == *vch)
                    {
                        self.table_iter = Some(iter);
                        return Some(affix);
                    }
                }
            }

            // Once that search is done, add the next character and start a new search into the
            // trie.
            let ch = self.chars.next()?;
            ch.hash(&mut self.hasher);
            let hash = self.hasher.finish();
            self.visited_chars.push(ch);

            // SAFETY: the lifetime of the returned value is bound to the table.
            let iter = unsafe { self.table.iter_hash(hash) };
            self.table_iter = Some(iter);
        }
    }
}

/// A collection of patterns used to break words into smaller words.
///
/// This is internally represented with a single `table` which is partitioned into three sections:
/// one for patterns that apply at the beginning of words, one for patterns that can apply
/// anywhere in the middle of a word, and one for patterns that must apply to the end of a word.
///
/// TODO: document how breaks are used and what the patterns mean.
pub(crate) struct BreakTable {
    table: Vec<String>,
    start_word_breaks_last_idx: usize,
    // Nuspell keeps the entries partitioned in the order "start, end, middle." I've re-arranged
    // this to be "start, middle, end" since I think it's more natural.
    middle_word_breaks_last_idx: usize,
}

impl From<Vec<&str>> for BreakTable {
    fn from(breaks: Vec<&str>) -> Self {
        let mut start = Vec::new();
        let mut middle = Vec::new();
        let mut end = Vec::new();

        for b in breaks.into_iter() {
            if b.is_empty() {
                // TODO: ensure this in the parsing code.
                unreachable!("break patterns must not be empty");
            }

            if let Some(b) = b.strip_prefix('^') {
                start.push(b.to_string());
            } else if let Some(b) = b.strip_suffix('$') {
                end.push(b.to_string());
            } else {
                middle.push(b.to_string());
            }
        }

        let mut table = start;
        let start_word_breaks_last_idx = table.len();
        table.append(&mut middle);
        let middle_word_breaks_last_idx = table.len();
        table.append(&mut end);

        Self {
            table,
            start_word_breaks_last_idx,
            middle_word_breaks_last_idx,
        }
    }
}

impl BreakTable {
    #[inline]
    pub fn start_word_breaks(&self) -> &[String] {
        &self.table[..self.start_word_breaks_last_idx]
    }

    #[inline]
    pub fn middle_word_breaks(&self) -> &[String] {
        &self.table[self.start_word_breaks_last_idx..self.middle_word_breaks_last_idx]
    }

    #[inline]
    pub fn end_word_breaks(&self) -> &[String] {
        &self.table[self.middle_word_breaks_last_idx..]
    }
}

pub(crate) enum CompoundRuleElement {
    Flag(Flag),
    ZeroOrOne,
    ZeroOrMore,
}

// Nuspell uses a `std::u16string` to represent this type which is quite clever. Nuspell can
// treat `?` and `*` like regular flags and therefore only use 2 bytes per element, since flags
// are all `char16_t`. The enum representation above takes 4 bytes per element.
//
// TODO: consider special-casing `*` and `?` when parsing. Instead of using an enum, encode them
// as `Flag`s. This will reduce the clarity of the code but save half of the space of each
// CompoundRule.
//
// Also look at real dictionaries and see how many compound rules there are. This may not be
// worth the reduction in clarity.
type CompoundRule = Vec<CompoundRuleElement>;

/// A set of rules that can be used to detect whether constructed compounds are allowed.
///
/// TODO: talk about wildcards, show a compounding example.
pub(crate) struct CompoundRuleTable {
    rules: Vec<CompoundRule>,
    all_flags: FlagSet,
}

impl FromIterator<CompoundRule> for CompoundRuleTable {
    fn from_iter<T: IntoIterator<Item = CompoundRule>>(iter: T) -> Self {
        let rules: Vec<_> = iter.into_iter().collect();

        let all_flags = rules
            .iter()
            .flatten()
            .filter_map(|el| match el {
                CompoundRuleElement::Flag(flag) => Some(*flag),
                _ => None,
            })
            .collect();

        Self { rules, all_flags }
    }
}

/// Storage for two `String`s within the allocation of one `String`.
pub(crate) struct StringPair {
    inner: String,
    /// The `.len()` of the first string: the index of the partition between the first and
    /// second string.
    partition: usize,
}

impl StringPair {
    pub fn new(left: &str, right: &str) -> Self {
        let mut inner = left.to_string();
        let partition = inner.len();
        inner.push_str(right);

        Self { inner, partition }
    }

    #[inline]
    pub fn left(&self) -> &str {
        &self.inner[..self.partition]
    }

    #[inline]
    pub fn right(&self) -> &str {
        &self.inner[self.partition..]
    }

    /// Get the partition point of the two strings. This is the same as the `.len()` of the
    /// [`left`] string.
    #[inline]
    pub fn left_len(&self) -> usize {
        self.partition
    }
}

pub(crate) struct CompoundPattern {
    begin_end_chars: StringPair,
    replacement: Option<String>,
    first_word_flag: Option<Flag>,
    second_word_flag: Option<Flag>,
    match_first_only_unaffixed_or_zero_affixed: bool,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn condition_parse() {
        assert_eq!(
            Err(ConditionError::EmptyCharacterClass),
            "[]".parse::<Condition>()
        );
        assert_eq!(
            Err(ConditionError::UnclosedCharacterClass),
            "[foo".parse::<Condition>()
        );
        assert_eq!(
            Err(ConditionError::UnopenedCharacterClass),
            "foo]".parse::<Condition>()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo".to_string(),
                chars: 3
            }),
            "foo".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo[bar]".to_string(),
                chars: 4
            }),
            "foo[bar]".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "[foo]bar".to_string(),
                chars: 4
            }),
            "[foo]bar".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo[bar]baz".to_string(),
                chars: 7
            }),
            "foo[bar]baz".parse()
        );
    }

    #[test]
    fn condition_matches() {
        // No special characters
        assert!("foo".parse::<Condition>().unwrap().matches("foo"));

        // Fast lane: the input is shorter (bytes) than the number of characters in the pattern.
        assert!(!"foo".parse::<Condition>().unwrap().matches("fo"));

        // Positive character class
        let condition = "xx[abc]x".parse::<Condition>().unwrap();
        assert!(condition.matches("xxax"));
        assert!(condition.matches("xxbx"));
        assert!(condition.matches("xxcx"));
        assert!(!condition.matches("xxdx"));

        // Negative character class
        let condition = "xx[^abc]x".parse::<Condition>().unwrap();
        assert!(!condition.matches("xxax"));
        assert!(!condition.matches("xxbx"));
        assert!(!condition.matches("xxcx"));
        assert!(condition.matches("xxdx"));
    }

    #[test]
    fn string_pair() {
        let pair = StringPair::new("foo", "bar");
        assert_eq!(pair.left(), "foo");
        assert_eq!(pair.right(), "bar");
        assert_eq!(pair.left_len(), 3);

        let pair = StringPair::new("", "");
        assert_eq!(pair.left(), "");
        assert_eq!(pair.right(), "");
        assert_eq!(pair.left_len(), 0);
    }
}
