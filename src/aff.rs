use crate::{
    alloc::{
        borrow::Cow,
        string::{String, ToString},
        vec::Vec,
    },
    Flag, FlagSet, WordList,
};

use core::{
    fmt,
    marker::PhantomData,
    str::{Chars, FromStr},
};

const HIDDEN_HOMONYM_FLAG: u16 = u16::MAX;
const MAX_SUGGESTIONS: usize = 16;

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

impl FromStr for FlagType {
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

impl fmt::Display for UnknownFlagTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "expected FLAG to be `long`, `num` or `UTF-8` if set, found {}",
            self.0
        )
    }
}

#[derive(Debug)]
pub enum ParseFlagError {
    NonAscii(char),
    MissingSecondChar(char),
    ParseIntError(core::num::ParseIntError),
    DuplicateComma,
    ZeroFlag,
    FlagAbove65535,
}

impl fmt::Display for ParseFlagError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonAscii(ch) => write!(f, "expected ascii char, found {}", ch),
            Self::MissingSecondChar(ch) => {
                write!(f, "expected two chars, {} is missing its second", ch)
            }
            Self::ParseIntError(err) => err.fmt(f),
            Self::DuplicateComma => f.write_str("unexpected extra comma"),
            Self::ZeroFlag => f.write_str("flag cannot be zero"),
            Self::FlagAbove65535 => f.write_str("flag's binary representation exceeds 65535"),
        }
    }
}

fn try_flag_from_u16(val: u16) -> Result<Flag, ParseFlagError> {
    Flag::new(val).ok_or(ParseFlagError::ZeroFlag)
}

fn try_flag_from_u32(val: u32) -> Result<Flag, ParseFlagError> {
    if val > u16::MAX as u32 {
        return Err(ParseFlagError::FlagAbove65535);
    }
    try_flag_from_u16(val as u16)
}

fn try_flag_from_char(ch: char) -> Result<Flag, ParseFlagError> {
    try_flag_from_u32(ch as u32)
}

impl FlagType {
    pub fn parse_flag_from_str(&self, input: &str) -> Result<Flag, ParseFlagError> {
        use ParseFlagError::*;
        assert!(!input.is_empty());

        match self {
            Self::Short => {
                let mut chars = input.chars();
                let ch = chars.next().expect("asserted to be non-empty above");
                if ch.is_ascii() {
                    // The flag is ASCII: it's a valid `u8` so it can fit into a `u16`.
                    try_flag_from_u16(ch as u16)
                } else {
                    Err(NonAscii(ch))
                }
            }
            Self::Long => {
                let mut chars = input.chars();
                let c1 = chars.next().expect("asserted to be non-empty above");
                if !c1.is_ascii() {
                    return Err(NonAscii(c1));
                }
                let c2 = match chars.next() {
                    Some(ch) => ch,
                    None => return Err(MissingSecondChar(c1)),
                };
                if !c2.is_ascii() {
                    return Err(NonAscii(c2));
                }

                try_flag_from_u16(u16::from_ne_bytes([c1 as u8, c2 as u8]))
            }
            Self::Numeric => {
                let number = input.parse::<u16>().map_err(ParseIntError)?;
                try_flag_from_u16(number)
            }
            Self::Utf8 => {
                let mut chars = input.chars();
                let ch = chars.next().expect("asserted to be non-empty above");
                try_flag_from_char(ch)
            }
        }
    }

    pub fn parse_flags_from_chars(&self, mut chars: Chars) -> Result<FlagSet, ParseFlagError> {
        use ParseFlagError::*;

        match self {
            Self::Short => {
                chars
                    .map(|ch| {
                        if ch.is_ascii() {
                            // The flag is ASCII: it's a valid `u8` so it can fit into a `u16`.
                            try_flag_from_u16(ch as u16)
                        } else {
                            Err(ParseFlagError::NonAscii(ch))
                        }
                    })
                    .collect()
            }
            Self::Long => {
                let mut flags = FlagSet::new();
                while let Some(c1) = chars.next() {
                    let c2 = match chars.next() {
                        Some(ch) => ch,
                        None => return Err(MissingSecondChar(c1)),
                    };
                    let flag = try_flag_from_u16(u16::from_ne_bytes([c1 as u8, c2 as u8]))?;
                    flags.insert(flag);
                }
                Ok(flags)
            }
            Self::Numeric => {
                let mut flags = FlagSet::new();
                let mut number = String::new();
                let mut separated = false;
                for ch in chars.by_ref() {
                    if ch.is_ascii_digit() {
                        number.push(ch);
                    } else {
                        if ch == ',' && separated {
                            return Err(DuplicateComma);
                        }
                        if ch == ',' {
                            separated = true;
                            let n = number.parse::<u16>().map_err(ParseIntError)?;
                            flags.insert(try_flag_from_u16(n)?);
                        }
                    }
                }
                Ok(flags)
            }
            Self::Utf8 => chars.map(try_flag_from_char).collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

impl fmt::Display for ConditionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl FromStr for Condition {
    type Err = ConditionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Affix<K> {
    /// The flag that words may use to reference this affix.
    flag: Flag,
    /// Whether the affix is compatible with the opposite affix.
    /// For example a word that has both a prefix and a suffix, both the prefix
    /// and suffix should have `crossproduct: true`.
    crossproduct: bool,
    /// What is stripped from the stem when the affix is applied.
    strip: Option<String>,
    /// What should be added when the affix is applied.
    add: String,
    /// Condition that the stem should be checked against to query if the
    /// affix is relevant.
    condition: Condition,
    /// Flags the affix has itself.
    flags: FlagSet,
    phantom_data: PhantomData<K>,
}

impl<K: AffixKind> Affix<K> {
    pub fn new(
        flag: Flag,
        crossproduct: bool,
        strip: Option<&str>,
        add: &str,
        condition: &str,
        flags: FlagSet,
    ) -> Result<Self, ConditionError> {
        Ok(Self {
            flag,
            crossproduct,
            strip: strip.map(|str| str.to_string()),
            add: add.to_string(),
            flags,
            condition: condition.parse()?,
            phantom_data: PhantomData,
        })
    }

    pub fn appending(&self) -> K::Chars<'_> {
        K::chars(&self.add)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct Pfx;
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct Sfx;

/// Rules for replacing characters at the beginning of a stem.
pub(crate) type Prefix = Affix<Pfx>;
/// Rules for replacing characters at the end of a stem.
pub(crate) type Suffix = Affix<Sfx>;

pub(crate) trait AffixKind {
    type Chars<'a>: Iterator<Item = char>
    where
        Self: 'a;

    fn chars(word: &str) -> Self::Chars<'_>;
}

impl AffixKind for Pfx {
    type Chars<'a> = Chars<'a>;

    fn chars(word: &str) -> Self::Chars<'_> {
        word.chars()
    }
}

impl AffixKind for Sfx {
    type Chars<'a> = core::iter::Rev<Chars<'a>>;

    fn chars(word: &str) -> Self::Chars<'_> {
        word.chars().rev()
    }
}

impl Prefix {
    /// Converts a word which starts with this `Prefix` to the word's stem.
    ///
    /// The prefix's `add` is removed from the beginning and replaced with the `strip`.
    ///
    /// Nuspell calls this `to_root`.
    ///
    /// # Panics
    ///
    /// This function `expect`s that the `Prefix`'s `add` is a prefix of the input `word`.
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        let stripped = word
            .strip_prefix(&self.add)
            .expect("to_stem should only be called when the `add` is a prefix of the word");

        match &self.strip {
            Some(strip) => {
                let mut stem = strip.to_string();
                stem.push_str(stripped);
                Cow::Owned(stem)
            }
            None => Cow::Borrowed(stripped),
        }
    }

    /// Converts a stem into a word starting with this `Prefix`.
    ///
    /// This prefix's `strip` is removed from the beginning and replaced with the `add`. This is
    /// the inverse of `Prefix::to_stem`.
    ///
    /// # Panics
    ///
    /// This function `expect`s that the given `word` starts with this `Prefix`'s `strip`, if this
    /// prefix has a `strip`.
    pub fn to_derived(&self, word: &str) -> String {
        let stripped = match &self.strip {
            Some(strip) => word
                .strip_prefix(strip)
                .expect("to_derived should only be called when `strip` is a prefix of the word"),
            None => word,
        };
        let mut stem = self.add.clone();
        stem.push_str(stripped);
        stem
    }

    pub fn condition_matches(&self, word: &str) -> bool {
        // Length in bytes is greater than or equal to length in chars.
        if word.len() < self.condition.chars {
            return false;
        }

        self.condition.matches(word)
    }
}

impl Suffix {
    /// Converts a word which ends with this `Suffix` to the word's stem.
    ///
    /// This suffix's `add` is removed from the end and replaced with the `strip`.
    ///
    /// Nuspell calls this `to_root`.
    ///
    /// # Panics
    ///
    /// This function `expect`s that the `Suffix`'s `add` is a suffix of the input `word`.
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        let stripped = word
            .strip_suffix(&self.add)
            .expect("to_stem should only be called when the `add` is a suffix of the word");

        match self.strip.as_deref() {
            Some(strip) => {
                let mut stem = stripped.to_string();
                stem.push_str(strip);
                Cow::Owned(stem)
            }
            None => Cow::Borrowed(stripped),
        }
    }

    /// Converts a stem into a word starting with this `Suffix`.
    ///
    /// This suffix's `strip` is removed from the end and replaced with the `add`. This is
    /// the inverse of `Suffix::to_stem`.
    ///
    /// # Panics
    ///
    /// This function `expect`s that the given `word` ends with this `Suffix`'s `strip`, if this
    /// suffix has a `strip`.
    pub fn to_derived(&self, word: &str) -> String {
        let mut stem = match &self.strip {
            Some(strip) => word
                .strip_suffix(strip)
                .expect("to_derived should only be called when `strip` is a prefix of the word"),
            None => word,
        }
        .to_string();
        stem.push_str(&self.add);
        stem
    }

    pub fn condition_matches(&self, word: &str) -> bool {
        // Length in bytes is greater than or equal to length in chars.
        if word.len() < self.condition.chars {
            return false;
        }

        let buffer = &mut [0; 4];
        let (chars, bytes) =
            word.chars()
                .rev()
                .take(self.condition.chars)
                .fold((0, 0), |(chars, bytes), ch| {
                    // TODO: convert to a u32 instead and check with bit math how many bytes
                    // the code point takes.
                    (chars + 1, bytes + ch.encode_utf8(buffer).len())
                });

        if chars < self.condition.chars {
            return false;
        }
        self.condition.matches(&word[word.len() - bytes..])
    }
}

pub(crate) type PrefixIndex = AffixIndex<Pfx>;
pub(crate) type SuffixIndex = AffixIndex<Sfx>;

/// A data structure for looking up any affixes which might match a given word.
///
/// The `AffixIndex` is one of two central data structures, along with the `WordList`. It
/// functions very similarly to a [radix tree], allowing efficient lookup of prefix or suffix
/// rules.
///
/// For example a prefix from `en_US.aff` for "re":
///
/// ```text
/// PFX A Y 1
/// PFX A   0     re         .
/// ```
///
/// That prefix strips nothing (`0`) from the beginning and adds "re" to the beginning of any
/// words it is applied to.
///
/// For prefixes, `affixes_of` returns an iterator over all of the `Prefix`es in the table which
/// have an `add` field which is a prefix of the search word.
///
/// This structure also searches from the end of the word when looking up suffixes. A suffix from
/// `en_US.aff`:
///
/// ```text
/// SFX D Y 4
/// SFX D   0     d          e
/// SFX D   y     ied        [^aeiou]y
/// SFX D   0     ed         [^ey]
/// SFX D   0     ed         [aeiou]y
/// ```
///
/// Any word in the word list with the "D" flag can try to apply these suffixes. For a word like
/// "aced," `affixes_of` would return the first, third and fourth suffixes, as `d`, `ed` and `ed`
/// are suffixes of "aced," but not the second (`ied`).
///
/// Internally this type is implemented using a sorted `Vec` of affixes - one table for prefixes
/// and one for suffixes. Iterating with `affixes_of` first emits all affixes with empty `add`
/// text. Then we look at the first character in the search string. We can constrain our search
/// to only the elements in the table that start with that character using a precomputed index
/// of characters to indices within the table. After considering the first character, we use
/// linear searches of the remaining table slice to constrain the search for each next character
/// in the search key.
///
/// [radix tree]: https://en.wikipedia.org/wiki/Radix_tree
// TODO: I originally tried a hashing-based approach using `hashbrown::raw::RawTable`. Lift that
// structure from the commit history and benchmark it against this Vec based approach.
#[derive(Debug)]
pub(crate) struct AffixIndex<K> {
    table: Vec<Affix<K>>,
    first_char: Vec<char>,
    prefix_idx_with_first_char: Vec<usize>,
}

impl<K: AffixKind> FromIterator<Affix<K>> for AffixIndex<K> {
    fn from_iter<T: IntoIterator<Item = Affix<K>>>(iter: T) -> Self {
        let mut table: Vec<_> = iter.into_iter().collect();
        // Sort the table lexiographically by key. We will use this lexiographical ordering to
        // efficiently search in AffixesIter.
        table.sort_unstable_by(|a, b| a.appending().cmp(b.appending()));

        let mut first_char = Vec::new();
        let mut prefix_idx_with_first_char = Vec::new();

        // Seek through the sorted table to the first element where the key is non-empty.
        let mut first_char_idx = table.partition_point(|affix| affix.appending().next().is_none());
        while first_char_idx < table.len() {
            let ch = table[first_char_idx]
                .appending()
                .next()
                .expect("vec is sorted so empty keys are before the partition point");

            // Save the first character of the key and the index of the affix in the table that
            // starts off this character. We can use this while reading the AffixIndex to jump
            // ahead efficiently in the table.
            first_char.push(ch);
            prefix_idx_with_first_char.push(first_char_idx);

            match table[first_char_idx..].iter().position(|affix| {
                affix
                    .appending()
                    .next()
                    .expect("vec is sorted so empty keys are before the partition point")
                    > ch
            }) {
                Some(next_char_index) => first_char_idx += next_char_index,
                None => break,
            }
        }
        // Add an extra element to the end so that `prefix_idx_with_first_char` is always one
        // element longer than `first_char`.
        prefix_idx_with_first_char.push(table.len());

        Self {
            table,
            first_char,
            prefix_idx_with_first_char,
        }
    }
}

impl<K: AffixKind> AffixIndex<K> {
    fn affixes_of<'a>(&'a self, word: &'a str) -> AffixesIter<'a, K> {
        AffixesIter {
            table: &self.table,
            first_char: &self.first_char,
            prefix_idx_with_first_char: &self.prefix_idx_with_first_char,
            chars: K::chars(word),
            chars_matched: 0,
        }
    }
}

/// An iterator over the affixes for the
pub(crate) struct AffixesIter<'a, K: AffixKind> {
    table: &'a [Affix<K>],
    first_char: &'a [char],
    prefix_idx_with_first_char: &'a [usize],
    chars: K::Chars<'a>,
    chars_matched: usize,
}

impl<'a, K: AffixKind> Iterator for AffixesIter<'a, K> {
    type Item = &'a Affix<K>;

    fn next(&mut self) -> Option<Self::Item> {
        // Return all affixes that append nothing first.
        if self.chars_matched == 0 {
            if self.table.is_empty() {
                return None;
            }

            let item = &self.table[0];
            if item.appending().next().is_some() {
                // The empty portion of the table is done.
                // Scan ahead to where the first character is.
                let ch = self.chars.next()?;
                let first_char_idx = self.first_char.iter().position(|c| *c == ch)?;

                // NOTE: `prefix_idx_with_first_char` always has at least one element and is
                // always one element longer than `first_char`, so we can safely index at `0`
                // and at whatever index we get from `first_char` plus one.
                let empty_offset = self.prefix_idx_with_first_char[0];
                // Constrain the bounds of the search to affixes that share the first letter
                // of the key. Offset by the number of affixes with empty `add` that we emitted
                // previously.
                let start = self.prefix_idx_with_first_char[first_char_idx] - empty_offset;
                let end = self.prefix_idx_with_first_char[first_char_idx + 1] - empty_offset;
                self.table = &self.table[start..end];
                self.chars_matched = 1;
            } else {
                self.table = &self.table[1..];
                return Some(item);
            }
        }

        loop {
            if self.table.is_empty() {
                return None;
            }

            // If the search key is exactly matched so far (up to the number of characters we've
            // seen), emit the item.
            let item = &self.table[0];
            if item.appending().count() == self.chars_matched {
                self.table = &self.table[1..];
                return Some(item);
            }

            // Look at the next character in the search key. Limit the search to the slice of
            // the table where the nth character for each affix matches this character of the
            // search key.
            let ch = self.chars.next()?;

            // Move `start` up to the index of the first affix that has this character in its
            // nth position.
            let char_beginning_idx = self
                .table
                .iter()
                .position(|affix| affix.appending().nth(self.chars_matched) == Some(ch))?;
            self.table = &self.table[char_beginning_idx..];

            // Move the `end` back so that the last element in the search slice is the last
            // affix that shares this character in its nth position.
            let char_end_idx = self
                .table
                .partition_point(|affix| affix.appending().nth(self.chars_matched) == Some(ch));
            self.table = &self.table[..char_end_idx];

            self.chars_matched += 1;
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

impl CompoundRuleTable {
    #[inline]
    pub fn has_any_flags(&self, flagset: &FlagSet) -> bool {
        self.all_flags.has_intersection(flagset)
    }
}

/// Storage for two `String`s within the allocation of one `String`.
#[derive(Debug)]
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

#[derive(Debug)]
pub(crate) struct CompoundPattern {
    begin_end_chars: StringPair,
    replacement: Option<String>,
    first_word_flag: Option<Flag>,
    second_word_flag: Option<Flag>,
    match_first_only_unaffixed_or_zero_affixed: bool,
}

pub(crate) struct AffData {
    // checking options
    pub words: WordList,
    prefixes: PrefixIndex,
    suffixes: SuffixIndex,
    complex_prefixes: bool,
    fullstrip: bool,
    checksharps: bool,
    forbid_warn: bool,
    compound_only_in_flag: Option<Flag>,
    circumfix_flag: Option<Flag>,
    forbidden_word_flag: Option<Flag>,
    keep_case_flag: Option<Flag>,
    need_affix_flag: Option<Flag>,
    warn_flag: Option<Flag>,
    break_table: BreakTable,
    // input_substr_replacer: ? TODO
    ignored_chars: String,
    // locale TODO
    // output_substr_replacer: ? TODO
    // compounding options
    compound_rules: CompoundRuleTable,
    compound_flag: Option<Flag>,
    compound_begin_flag: Option<Flag>,
    compound_middle_flag: Option<Flag>,
    compound_last_flag: Option<Flag>,
    compound_min_length: u16,
    compound_max_word_count: u16,
    compound_permit_flag: Option<Flag>,
    compound_forbid_flag: Option<Flag>,
    compound_force_uppercase: Option<Flag>,
    compound_more_suffixes: bool,
    compound_check_duplicate: bool,
    compound_check_rep: bool,
    compound_check_case: bool,
    compound_check_triple: bool,
    compound_syllable_num: bool,
    compound_syllable_max: u16,
    compound_syllable_vowels: String,
    compound_patterns: Vec<CompoundPattern>,
    max_compound_suggestions: u16,
    // suggestion options
    // replacements: ReplacementTable,
    // similarities: Vec<SimilarityGroup>,
    // keyboard_closeness: String,
    // try_chars: String,
    // phonetic_table: PhoneticTable,
    nosuggest_flag: Option<Flag>,
    substandard_flag: Option<Flag>,
    max_ngram_suggestions: u16,
    max_diff_factor: Option<u16>,
    only_max_diff: bool,
    no_split_suggestions: bool,
    suggest_with_dots: bool,
    // options only used while parsing
    flag_type: FlagType,
    // encoding: Encoding,
    flag_aliases: Vec<FlagSet>,
    // wordchars: String, deprecated?
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::*;

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

    #[test]
    fn empty_affix_index() {
        let index: PrefixIndex = [].into_iter().collect();
        assert!(index.affixes_of("anything").next().is_none());

        let index: SuffixIndex = [].into_iter().collect();
        assert!(index.affixes_of("anything").next().is_none());
    }

    #[test]
    fn affix_index_prefix_multiset_nuspell_unit_test() {
        // Upstream: <https://github.com/nuspell/nuspell/blob/b37faff6ea630a4a1bfb22097d455224b4239f8e/tests/unit_test.cxx#L315-L329>
        fn prefix(add: &str) -> Prefix {
            Prefix::new(Flag::new(1).unwrap(), true, None, add, ".", flagset![]).unwrap()
        }

        let index: PrefixIndex = [
            "", "a", "", "ab", "abx", "as", "asdf", "axx", "as", "bqwe", "ba", "rqwe",
        ]
        .into_iter()
        .map(prefix)
        .collect();

        let prefixes: Vec<_> = index
            .affixes_of("asdfg")
            .map(|prefix| prefix.add.as_str())
            .collect();

        assert_eq!(&["", "", "a", "as", "as", "asdf"], prefixes.as_slice());
    }

    #[test]
    fn affix_index_suffix_multiset_nuspell_unit_test() {
        // Upstream: <https://github.com/nuspell/nuspell/blob/b37faff6ea630a4a1bfb22097d455224b4239f8e/tests/unit_test.cxx#L331-L345>
        fn suffix(add: &str) -> Suffix {
            Suffix::new(Flag::new(1).unwrap(), true, None, add, ".", flagset![]).unwrap()
        }

        let index: SuffixIndex = [
            "", "", "a", "b", "b", "ab", "ub", "zb", "aub", "uub", "xub", "huub",
        ]
        .into_iter()
        .map(suffix)
        .collect();

        let suffixes: Vec<_> = index
            .affixes_of("ahahuub")
            .map(|suffix| suffix.add.as_str())
            .collect();

        assert_eq!(
            &["", "", "b", "b", "ub", "uub", "huub"],
            suffixes.as_slice()
        );
    }

    #[test]
    fn affix_index_en_us_suffix_example() {
        // This suffix is from `en_US.aff`:
        //
        // SFX D Y 4
        // SFX D   0     d          e
        // SFX D   y     ied        [^aeiou]y
        // SFX D   0     ed         [^ey]
        // SFX D   0     ed         [aeiou]y
        let flag = Flag::new('D' as u16).unwrap();
        let suffix1 = Suffix::new(flag, true, None, "d", "e", flagset![]).unwrap();
        let suffix2 = Suffix::new(flag, true, Some("y"), "ied", "[^aeiou]y", flagset![]).unwrap();
        let suffix3 = Suffix::new(flag, true, None, "ed", "[^ey]", flagset![]).unwrap();
        let suffix4 = Suffix::new(flag, true, None, "ed", "[aeiou]y", flagset![]).unwrap();

        let index: SuffixIndex = [&suffix1, &suffix2, &suffix3, &suffix4]
            .into_iter()
            .cloned()
            .collect();

        // From `en_US.dic`: `ace/DSMG`. The "ace" stem can be turned into "aced" with the above
        // suffix rules, specifically the first rule (`suffix1`). However all of these suffixes
        // except `suffix2` are returned by `affixes_of`.
        let word = "aced";
        let affixes: Vec<&Suffix> = index.affixes_of(word).collect();
        assert_eq!(&[&suffix1, &suffix3, &suffix4], affixes.as_slice());

        // Note: even though the condition can match, we would also need to look up the produced
        // stem in the word list to confirm that "aced" is a valid word.

        let stem1 = suffix1.to_stem(word);
        assert_eq!(&stem1, "ace");
        assert!(suffix1.condition_matches(&stem1));

        let stem3 = suffix3.to_stem(word);
        assert_eq!(&stem3, "ac");
        assert!(suffix3.condition_matches(&stem3));

        let stem4 = suffix4.to_stem(word);
        assert_eq!(&stem4, "ac");
        assert!(!suffix4.condition_matches(&stem4));
    }
}
