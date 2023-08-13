//! Configuration and rulesets for a dictionary.
//! This comes from Hunspell `.aff` files, hence the name of the module & struct.

// TODO: remove this once parsing and suggestion are done.
#![allow(dead_code)]

mod index;

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::Rc,
};

use regex::Regex;

use crate::{checker::AffixForm, Flag, FlagSet};

use self::index::AffixIndex;

#[derive(Debug)]
pub(crate) struct Aff {
    // General
    /// Encoding of the `.aff` and `.dic` files
    /// From the SET command.
    // TODO do we need this? Or can we require that incoming text is UTF8?
    pub encoding: String,
    /// Encoding for flags.
    /// From the FLAG command.
    pub flag_type: FlagType,
    /// ISO language code. This is used to special-case languages like Turkic languages
    /// which use special rules for I/i capitalization.
    /// From the LANG command.
    pub language_id: Option<String>,
    /// Characters to ignore in dictionary words, affixes and input words.
    /// From the IGNORE command.
    pub ignore_chars: Option<IgnoreChars>,
    /// Whether the language has sharps (ß)
    /// From the CHECKSHARPS command.
    pub check_sharps: bool,
    /// The flag marking words as forbidden so that they are rejected by check
    /// and suggest. This is necessary because some compounding and affix rules
    /// may produce a theoretically- but not actually correct word.
    /// From the FORBIDDENWORD command.
    pub forbidden_word_flag: Option<Flag>,
    /// Flag to mark words that shouldn't be considered correct unless their case
    /// matches the dictionary exactly.
    /// From the KEEPCASE command.
    pub keep_case_flag: Option<Flag>,

    // Suggestions
    /// Flag to mark a word of affix so that it is not produced by suggest.
    /// From the NOSUGGEST command.
    pub no_suggest_flag: Option<Flag>,
    /// A specification of adjacent characters on a keyboard used for typo
    /// detection.
    /// From the KEY command.
    pub key: String,
    /// A list of characters to try with earlier characters being more probably
    /// than later characters.
    /// From the TRY command.
    pub try_chars: String,
    /// Table of replacaements for common spelling mistakes.
    /// From the REP command.
    pub replacements: Vec<ReplacementPattern>,
    /// Sets of similar characters to try when suggesting corrections.
    /// For example `aáã`.
    /// From the MAP command.
    pub map_chars: Vec<HashSet<char>>,
    /// A toggle that controls whether split words should be suggested.
    /// Required for Swedish.
    /// From the NOSPLITSUGS command.
    pub no_split_suggestions: bool,
    // /// Table for metaphone transformations.
    // /// From the PHONE command.
    // pub phonet_table: Option<PhonetTable>,
    /// A limit on the number of compound suggestions.
    /// From the MAXCPDSUGS command.
    pub max_compound_suggestions: usize,

    // NGram suggestions
    /// A maximum number of n-gram suggestions.
    /// From the MAXNGRAMSUGS command.
    pub max_ngram_suggestions: usize,
    /// Sets the similarity factor for the n-gram based suggestions.
    /// From the MAXDIFF command.
    pub max_diff: usize,
    /// Remove all bad n-gram suggestions.
    /// From the ONLYMAXDIFF command.
    pub only_max_diff: bool,

    // Stemming
    /// Dictionary of prefixes organized by flag.
    /// From the PFX command.
    pub prefixes: HashMap<Flag, Vec<Rc<Prefix>>>,
    /// Dictionary of suffixes organized by flag.
    /// From the SFX command.
    pub suffixes: HashMap<Flag, Vec<Rc<Suffix>>>,
    /// From the NEEDAFFIX command.
    pub need_affix_flag: Option<Flag>,
    /// From the CIRCUMFIX command.
    pub circumfix_flag: Option<Flag>,
    /// From the COMPLEXPREFIXES command.
    pub complex_prefixes: bool,
    /// From the FULLSTRIP command.
    pub full_strip: bool,
    /// From the BREAK command.
    pub break_patterns: Vec<BreakPattern>,
    /// From the COMPOUNDRULE command.
    pub compound_rules: Vec<CompoundRule>,
    /// Minimum length of words used for compounding.
    /// From the COMPOUNDMIN command.
    pub compound_min_length: usize,
    /// From the COMPOUNDWORDMAX command.
    pub max_compound_word_count: Option<usize>,
    /// From the COMPOUNDFLAG command.
    pub compound_flag: Option<Flag>,
    /// From the COMPOUNDBEGIN command.
    pub compound_begin_flag: Option<Flag>,
    /// From the COMPOUNDMIDDLE command.
    pub compound_middle_flag: Option<Flag>,
    /// From the COMPOUNDEND command.
    pub compound_end_flag: Option<Flag>,
    /// From the ONLYINCOMPOUND command.
    pub only_in_compound_flag: Option<Flag>,
    /// From the COMPOUNDPERMITFLAG command.
    pub compound_permit_flag: Option<Flag>,
    /// From the COMPOUNDFORBIDFLAG command.
    pub compound_forbid_flag: Option<Flag>,
    /// From the FORCEUCASE command.
    pub force_uppercase_flag: Option<Flag>,
    /// Whether to forbid capitalized characters at word boundaries in compounds.
    /// From the CHECKCOMPOUNDCASE command.
    pub check_compound_case: bool,
    /// Whether to forbid word duplication in compounds.
    /// From the CHECKCOMPOUNDDUP command.
    pub check_compound_dupe: bool,
    /// Whether to forbid compounding if the compound word might be a non-compound
    /// word via some replacement in the REP table.
    /// From the CHECKCOMPOUNDREP command.
    pub check_compound_replacement: bool,
    /// Whether to forbid compounds that lead to triple repeating letters.
    /// From the CHECKCOMPOUNDTRIPLE command.
    pub check_compound_triple: bool,
    /// Whether to forbid compounds when a pair of words in the compound match
    /// patterns in this list.
    /// From the CHECKCOMPOUNDPATTERN command.
    pub check_compound_pattern: Vec<CompoundPattern>,
    /// Whether to allow simplified 2-letter forms of the compound forbidden by
    /// CHECKCOMPOUNDTRIPLE.
    /// From the SIMPLIFIEDTRIPLE command.
    pub simplified_triple: bool,
    /// Allow twofold suffixes within compounds.
    /// From the COMPOUNDMORESUFFIXES command.
    pub compound_more_suffixes: bool,

    // Pre/post processing
    /// Conversions to make to words before checking or suggesting based on them.
    /// From the ICONV command.
    pub input_conversion: Option<ConversionTable>,
    /// Conversions to make to words before returning them.
    /// From the OCONV command.
    pub output_conversion: Option<ConversionTable>,
    /// A table of flag-set aliases.
    /// The first flag-set in the vec is an alias that can replace "1", the
    /// second "2", and so on.
    /// From the AF command.
    pub flag_set_aliases: Vec<FlagSet>,
    /// ?
    /// From the AM command.
    pub word_aliases: HashMap<String, HashSet<String>>,
    // ---
    // Not implemented in Spellbook:
    // * WARN
    // * FORBIDWARN
    // * SYLLABLENUM
    // * COMPOUNDROOT
    // * COMPOUNDSYLLABLE
    // * SUBSTANDARD
    // * LEMMA_PRESENT
    // * WORDCHARS
    // ---
    pub casing: Casing,
    pub suffixes_index: AffixIndex<Vec<Rc<Suffix>>>,
    pub prefixes_index: AffixIndex<Vec<Rc<Prefix>>>,
}

impl Default for Aff {
    fn default() -> Self {
        Self {
            encoding: Default::default(),
            flag_type: Default::default(),
            language_id: Default::default(),
            ignore_chars: Default::default(),
            check_sharps: Default::default(),
            forbidden_word_flag: Default::default(),
            key: String::from("qwertyuiop|asdfghjkl|zxcvbnm"),
            try_chars: Default::default(),
            no_suggest_flag: Default::default(),
            keep_case_flag: Default::default(),
            replacements: Default::default(),
            map_chars: Default::default(),
            no_split_suggestions: Default::default(),
            max_compound_suggestions: 3,
            max_ngram_suggestions: 4,
            // Docs say this is the default but spylls has this as -1.
            max_diff: 5,
            only_max_diff: Default::default(),
            prefixes: Default::default(),
            suffixes: Default::default(),
            need_affix_flag: Default::default(),
            circumfix_flag: Default::default(),
            complex_prefixes: Default::default(),
            full_strip: Default::default(),
            break_patterns: Default::default(),
            compound_rules: Default::default(),
            compound_min_length: 3,
            max_compound_word_count: Default::default(),
            compound_flag: Default::default(),
            compound_begin_flag: Default::default(),
            compound_middle_flag: Default::default(),
            compound_end_flag: Default::default(),
            only_in_compound_flag: Default::default(),
            compound_permit_flag: Default::default(),
            compound_forbid_flag: Default::default(),
            force_uppercase_flag: Default::default(),
            check_compound_case: Default::default(),
            check_compound_dupe: Default::default(),
            check_compound_replacement: Default::default(),
            check_compound_triple: Default::default(),
            check_compound_pattern: Default::default(),
            simplified_triple: Default::default(),
            compound_more_suffixes: Default::default(),
            input_conversion: Default::default(),
            output_conversion: Default::default(),
            flag_set_aliases: Default::default(),
            word_aliases: Default::default(),
            casing: Default::default(),
            suffixes_index: Default::default(),
            prefixes_index: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Capitalization {
    /// Hunspell: "NO"
    Lower,
    /// Hunspell: "INIT"
    Title,
    /// Hunspell: "ALL"
    Upper,
    /// Hunspell: "HUH"
    Camel,
    /// Hunspell: "HUHINIT"
    Pascal,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) enum Casing {
    Germanic,
    Turkic,
    #[default]
    Other,
}

impl Casing {
    // TODO: take casings into account.
    pub(crate) fn guess(&self, word: &str) -> Capitalization {
        // TODO: use nuspell's 'guess' instead?
        if word.chars().all(|ch| ch.is_lowercase()) {
            Capitalization::Lower
        } else if word.chars().all(|ch| ch.is_uppercase()) {
            Capitalization::Upper
        } else if word
            .chars()
            .next()
            .expect("word is non-empty")
            .is_uppercase()
        {
            if word.chars().skip(1).all(|ch| ch.is_lowercase()) {
                Capitalization::Title
            } else {
                Capitalization::Pascal
            }
        } else {
            Capitalization::Camel
        }
    }

    /// Guess how the word might have been cased in the dictionary,
    /// assuming that it is spell correctly.
    /// For example if the word is "Kitten" guesses might be "kitten"
    /// and "KITTEN".
    pub(crate) fn variants<'a>(&self, word: &'a str) -> (Capitalization, Vec<Cow<'a, str>>) {
        let capitalization = self.guess(word);
        let mut variants = vec![Cow::Borrowed(word)];

        match capitalization {
            Capitalization::Lower | Capitalization::Camel => (),
            Capitalization::Title => variants.append(&mut self.lower(word)),
            Capitalization::Pascal => variants.append(&mut self.lower_first(word)),
            Capitalization::Upper => {
                variants.append(&mut self.lower(word));
                variants.append(&mut self.capitalize(word));
            }
        }

        (capitalization, variants)
    }

    pub(crate) fn lower<'a>(&self, word: &'a str) -> Vec<Cow<'a, str>> {
        // Can't be properly downcased in non-Turkic casings.
        if word.chars().next().expect("word is non-empty") == 'İ' {
            return vec![];
        }

        // TODO: do we have to switch over to unicode_segmentation to make this work?
        // Can we use chars so cavalierly?
        vec![Cow::Owned(word.to_lowercase().replace("i̇", "i"))]
    }

    pub(crate) fn lower_first<'a>(&self, word: &'a str) -> Vec<Cow<'a, str>> {
        self.lower(word)
            .iter()
            .map(|word| {
                let ch = word.chars().next().expect("word is non-empty");
                Cow::Owned(if ch.is_uppercase() {
                    std::iter::once(ch)
                        .chain(word.chars().skip(1))
                        .collect::<String>()
                } else {
                    word.to_string()
                })
            })
            .collect()
    }

    pub(crate) fn upper<'a>(&self, word: &'a str) -> Vec<Cow<'a, str>> {
        vec![Cow::Owned(word.to_uppercase())]
    }

    pub(crate) fn capitalize<'a>(&self, word: &'a str) -> Vec<Cow<'a, str>> {
        let mut chars = word.chars().peekable();
        let ch = chars.next().expect("word is non-empty");
        if chars.peek().is_none() {
            if ch.is_uppercase() {
                vec![Cow::Borrowed(word)]
            } else {
                vec![Cow::Owned(word.to_uppercase())]
            }
        } else {
            let rest: String = chars.collect();
            self.lower(&rest)
                .iter()
                .flat_map(move |word| {
                    ch.to_uppercase().map(move |ch| {
                        let mut w2 = String::with_capacity(word.len() + 1);
                        w2.push(ch);
                        w2.push_str(word);
                        Cow::Owned(w2)
                    })
                })
                .collect()
        }
    }
}

/// Hunspell calls this the flag "type" but it's more about the
/// encoding and representation of flags.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) enum FlagType {
    /// Each flag is a single ASCII character
    #[default]
    Short,
    /// Each flag is two ASCII characters
    Long,
    /// Each flag is a number in the range `1..=65000`.
    /// (We'll approximate that to `2^16`.) Flags in sequences
    /// are separated by commas.
    Numeric,
    /// Each flag is one UTF-8 character.
    Utf8,
}

#[derive(Debug)]
pub(crate) enum ParseFlagError {
    NonAscii(char),
    MissingSecondChar(char),
    Empty,
    ParseIntError(std::num::ParseIntError),
    DuplicateComma,
}

impl FlagType {
    pub fn parse_flag_from_str(&self, input: &str) -> Result<Flag, ParseFlagError> {
        use ParseFlagError::*;

        if input.is_empty() {
            return Err(Empty);
        }

        match self {
            Self::Short => {
                let mut chars = input.chars();
                let ch = chars.next().expect("asserted to be non-empty above");
                if ch.is_ascii() {
                    Ok(ch as Flag)
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

                Ok(u16::from_ne_bytes([c1 as u8, c2 as u8]) as Flag)
            }
            Self::Numeric => {
                let number = input.parse::<u16>().map_err(ParseIntError)?;
                Ok(number as Flag)
            }
            Self::Utf8 => {
                let mut chars = input.chars();
                let ch = chars.next().expect("asserted to be non-empty above");
                Ok(ch as Flag)
            }
        }
    }

    pub fn parse_flag_from_char(&self, ch: char) -> Result<Flag, ParseFlagError> {
        match self {
            Self::Short => {
                if ch.is_ascii() {
                    Ok(ch as Flag)
                } else {
                    Err(ParseFlagError::NonAscii(ch))
                }
            }
            Self::Utf8 => Ok(ch as Flag),
            _ => unreachable!("parse_flag_from_char only supports short or UTF8 flag types"),
        }
    }

    pub fn parse_flags_from_chars(
        &self,
        mut chars: std::str::Chars,
    ) -> Result<FlagSet, ParseFlagError> {
        use ParseFlagError::*;

        match self {
            Self::Long => {
                let mut flags = FlagSet::new();
                while let Some(c1) = chars.next() {
                    let c2 = match chars.next() {
                        Some(ch) => ch,
                        None => return Err(MissingSecondChar(c1)),
                    };
                    flags.insert(u16::from_ne_bytes([c1 as u8, c2 as u8]) as Flag);
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
                    } else if ch == ',' && separated {
                        return Err(DuplicateComma);
                    } else if ch == ',' {
                        separated = true;
                        let n = number.parse::<u16>().map_err(ParseIntError)?;
                        flags.insert(n as Flag);
                    }
                }
                Ok(flags)
            }
            Self::Short | Self::Utf8 => {
                let flags = chars
                    .map(|ch| self.parse_flag_from_char(ch))
                    .collect::<Result<FlagSet, _>>()?;
                Ok(flags)
            }
        }
    }

    // #[cfg(test)]
    // pub(crate) fn parse_flags_from_str(&self, input: &str) -> Result<FlagSet, ParseFlagError> {
    //     self.parse_flags_from_chars(input.chars())
    // }
}

#[derive(Debug, Default)]
pub(crate) struct IgnoreChars(HashSet<char>);

impl IgnoreChars {
    pub(crate) fn erase_ignored<'a>(&self, word: &'a str) -> Cow<'a, str> {
        let is_ignored = |ch: char| self.0.contains(&ch);

        if word.chars().any(is_ignored) {
            Cow::Owned(word.replace(is_ignored, ""))
        } else {
            Cow::Borrowed(word)
        }
    }
}

/// Rules for replacing characters at the beginning of a stem.
#[derive(Debug)]
pub(crate) struct Prefix(Affix);

impl Prefix {
    pub fn new(
        flag: Flag,
        crossproduct: bool,
        strip: &str,
        add: &str,
        condition: &str,
        flags: FlagSet,
    ) -> Result<Self, regex::Error> {
        let condition_regex = Regex::new(&format!("^{}", condition.replace('-', "\\-")))?;
        let replace_regex = Regex::new(&format!("^{add}"))?;

        Ok(Self(Affix {
            flag,
            crossproduct,
            strip: strip.to_string(),
            add: add.to_string(),
            condition: condition.to_string(),
            flags,
            condition_regex,
            replace_regex,
        }))
    }
}

impl Deref for Prefix {
    type Target = Affix;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Rules for replacing characters at the end of a stem.
#[derive(Debug)]
pub(crate) struct Suffix(Affix);

impl Suffix {
    pub fn new(
        flag: Flag,
        crossproduct: bool,
        strip: &str,
        add: &str,
        condition: &str,
        flags: FlagSet,
    ) -> Result<Self, regex::Error> {
        let condition_regex = Regex::new(&format!("{}$", condition.replace('-', "\\-")))?;
        let replace_regex = Regex::new(&format!("{add}$"))?;

        Ok(Self(Affix {
            flag,
            crossproduct,
            strip: strip.to_string(),
            add: add.to_string(),
            condition: condition.to_string(),
            flags,
            condition_regex,
            replace_regex,
        }))
    }
}

impl Deref for Suffix {
    type Target = Affix;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Internal container type for a prefix or suffix.
#[derive(Debug)]
pub(crate) struct Affix {
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
    pub condition: String,
    /// Flags the affix has itself.
    pub flags: FlagSet,
    /// A regex that checks whether the condition matches.
    pub condition_regex: Regex,
    /// TODO
    pub replace_regex: Regex,
}

#[derive(Debug)]
pub(crate) struct BreakPattern(Regex);

impl Deref for BreakPattern {
    type Target = Regex;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl BreakPattern {
    // TODO: remove wrapper type?
    pub fn new(pattern: &str) -> Result<Self, regex::Error> {
        let pattern = regex::escape(pattern)
            .replace("\\^", "^")
            .replace("\\$", "$");
        if pattern.starts_with('^') || pattern.ends_with('$') {
            Regex::new(&format!("({pattern})")).map(Self)
        } else {
            Regex::new(&format!(".({pattern}).")).map(Self)
        }
    }
}

#[derive(Debug)]
pub(crate) struct ReplacementPattern {
    pub pattern: Regex,
    pub replacement: String,
}

impl ReplacementPattern {
    pub fn new(pattern: &str, replacement: &str) -> Result<Self, regex::Error> {
        let pattern = Regex::new(pattern)?;

        Ok(Self {
            pattern,
            replacement: replacement.to_string(),
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum FlagPatternWildcard {
    /// The '?' wildcard from regex, matching or ignoring the previous flag.
    ZeroOrOne,
    /// The '*' wildcard from regex, matching the previous flag any number
    /// of times.
    ZeroOrMore,
}

/// A set of formulas for combining words together via flags.
///
/// We can't reuse Regex here for checking matches because flags are
/// not represented as valid strings. The pattern only needs to support
/// '*' and '?' wildcards/rules, though, so we roll our Regex-like
/// pattern matcher.
///
/// From the COMPOUNDRULE command.
#[derive(Debug, Clone)]
pub(crate) struct CompoundRule {
    /// The flags in the pattern in order along with their modifiers.
    pattern: Vec<(Flag, Option<FlagPatternWildcard>)>,
}

// TODO rename or merge into a larger error type.
#[derive(Debug)]
pub(crate) enum ParseCompoundRuleError {
    Flag(ParseFlagError),
    DanglingWildcard(char),
    NestedParentheses,
    DanglingParenthesis(char),
}

impl From<ParseFlagError> for ParseCompoundRuleError {
    fn from(err: ParseFlagError) -> Self {
        Self::Flag(err)
    }
}

impl CompoundRule {
    pub fn new(text: &str, flag_type: FlagType) -> Result<Self, ParseCompoundRuleError> {
        use FlagPatternWildcard::{ZeroOrMore, ZeroOrOne};
        use ParseCompoundRuleError::*;

        let wildcard = |ch: char| match ch {
            '*' => ZeroOrMore,
            '?' => ZeroOrOne,
            _ => unreachable!(),
        };

        let mut pattern = Vec::new();
        match flag_type {
            FlagType::Short | FlagType::Utf8 => {
                let mut chars = text.chars().peekable();
                while let Some(ch) = chars.next() {
                    if ch == '?' || ch == '*' {
                        return Err(DanglingWildcard(ch));
                    }

                    let flag = flag_type.parse_flag_from_char(ch)?;
                    let wildcard = chars.peek().copied().and_then(|ch| match ch {
                        '*' | '?' => {
                            chars.next();
                            Some(wildcard(ch))
                        }
                        _ => None,
                    });
                    pattern.push((flag, wildcard));
                }
            }
            // These flag types surround each flag in parens. For example
            // `(aa)(bb)*(cc)` or `(101)(102)?(103)`.
            FlagType::Long | FlagType::Numeric => {
                let mut in_paren = false;
                let mut word = String::new();
                for ch in text.chars() {
                    match ch {
                        '(' if in_paren => return Err(NestedParentheses),
                        '(' => in_paren = true,
                        ')' if in_paren => {
                            // parse that word as a flag
                            let flag = flag_type.parse_flag_from_str(&word)?;
                            word.clear();
                            pattern.push((flag, None));
                        }
                        ')' => return Err(DanglingParenthesis(')')),
                        '*' | '?' => match pattern.last_mut() {
                            Some(atom) if atom.1.is_some() => return Err(DanglingWildcard(ch)),
                            Some(atom) => atom.1 = Some(wildcard(ch)),
                            None => return Err(DanglingWildcard(ch)),
                        },
                        _ => word.push(ch),
                    }
                }
                if in_paren {
                    return Err(DanglingParenthesis('('));
                }
            }
        }

        Ok(Self { pattern })
    }

    /// Check whether the compound rule matches the guess flags
    /// fully: so that the entire pattern matches all of the flags.
    pub fn full_match(&self, flag_sets: &[&FlagSet]) -> bool {
        Self::match_impl(&self.pattern, flag_sets, false, false)
    }

    /// Check whether the compound rule matches the guess flags
    /// partially: so that at least some amount of the start of the
    /// pattern matches all of the flags.
    pub fn partial_match(&self, flag_sets: &[&FlagSet]) -> bool {
        Self::match_impl(&self.pattern, flag_sets, false, true)
    }

    fn match_impl(
        pattern: &[(Flag, Option<FlagPatternWildcard>)],
        guess: &[&FlagSet],
        is_partial: bool,
        allow_partial: bool,
    ) -> bool {
        use FlagPatternWildcard::*;

        // If we decide that the pattern doesn't match at this stage in the
        // match, we could still return true if partial matches are allowed
        // and we have partially matched some of the pattern.
        let no_match = allow_partial && is_partial;

        if pattern.is_empty() {
            return if guess.is_empty() { true } else { no_match };
        } else if guess.is_empty() {
            return no_match;
        }

        let (flag, wildcard) = &pattern[0];
        let pattern_rest = &pattern[1..];
        let flag_set = &guess[0];
        let guess_rest = &guess[1..];
        let flag_in_set = flag_set.contains(flag);

        (match (wildcard, flag_in_set) {
            // '*'
            (Some(ZeroOrMore), true) => {
                // Assume that the flag doesn't consume the wildcard.
                Self::match_impl(pattern, guess_rest, true, allow_partial)
                    // Assume that the flag consumes the wildcard.
                    || Self::match_impl(pattern_rest, guess_rest, true, allow_partial)
                    // Assume that the flag matched zero times instead.
                    || Self::match_impl(pattern_rest, guess, is_partial, allow_partial)
            }
            // '?'
            (Some(ZeroOrOne), true) => {
                // Assume that the flag consumes the '?'. Same as if the '?' wildcard
                // wasn't present, i.e. `(None, true)`.
                Self::match_impl(pattern_rest, guess_rest, true, allow_partial)
                    // Assume that the zero part of the pattern was intended here instead.
                    // Discard the part and check the remaining pattern against the guess
                    // without advancing the guess.  Same as if the flag didn't match,
                    // i.e. `(Some(ZeroOrOne), false)`.
                    || Self::match_impl(pattern_rest, guess, is_partial, allow_partial)
            }
            // '?' or '*'
            (Some(ZeroOrMore | ZeroOrOne), false) => {
                // Assume that the flag matched zero times.
                Self::match_impl(pattern_rest, guess, is_partial, allow_partial)
            }
            // No wildcard.
            (None, true) => Self::match_impl(pattern_rest, guess_rest, true, allow_partial),
            (None, false) => false,
        }) || no_match
    }
}

/// A pattern to check whether a compound word is correct.
/// From the CHECKCOMPOUNDPATTERN rule.
#[derive(Debug)]
pub(crate) struct CompoundPattern {
    left_stem: String,
    left_flag: Option<Flag>,
    left_no_affix: bool,
    right_stem: String,
    right_flag: Option<Flag>,
    right_no_affix: bool,
    // Complicated and not used in any known dictionary, so this part is ignored
    // and unimplemented.
    _replacement: Option<String>,
}

impl CompoundPattern {
    pub fn new(_left: &str, _right: &str) -> Self {
        // This is used by a handful of dictionaries.
        unimplemented!()
    }

    pub fn r#match(&self, left: &AffixForm, right: &AffixForm) -> bool {
        use crate::stdx::is_none_or;

        left.stem.ends_with(&self.left_stem)
            && right.stem.starts_with(&self.right_stem)
            && (!self.left_no_affix || !left.is_base())
            && (!self.right_no_affix || !right.is_base())
            && (is_none_or(self.left_flag, |flag| left.flags().contains(&flag)))
            && (is_none_or(self.right_flag, |flag| right.flags().contains(&flag)))
    }
}

// Split a line into a word and set of flags.
// Note that `/` can be escaped in a word with a backslash.
// TODO: find a home for this function.
// fn split_word_and_flags(
//     input: &str,
//     flag_type: FlagType,
//     ignore_chars: &[char],
// ) -> Result<(String, FlagSet), ParseFlagError> {
//     let mut chars = input.chars();
//     let mut word = String::new();
//     let mut escape = false;
//     for ch in chars.by_ref() {
//         match ch {
//             '\\' => escape = !escape,
//             ch if ignore_chars.contains(&ch) => (),
//             '/' if !escape => break,
//             _ => word.push(ch),
//         }
//     }
//     let flag_set = flag_type.parse_flags_from_chars(chars)?;
//
//     Ok((word, flag_set))
// }

/// Table of conversions that should be applied before or after processing.
/// processing.
///
/// This is currently simplified to ignore patterns that show up only in Hunspells
/// test harness but not in actual dictionaries.
///
/// From ICONV and/or OCONV.
#[derive(Debug, Default)]
pub(crate) struct ConversionTable {
    // Note: ignoring the hidden feature in Hunspell that `_` acts
    // as an anchor in the patterns.
    conversions: Vec<(String, String)>,
}

impl ConversionTable {
    pub fn new(conversions: &[(&str, &str)]) -> Self {
        let mut conversions: Vec<_> = conversions
            .iter()
            .map(|(pattern, replacement)| (pattern.to_string(), replacement.to_string()))
            .collect();
        // Sort patterns by max length.
        conversions.sort_unstable_by_key(|(pattern, _)| std::cmp::Reverse(pattern.chars().count()));
        Self { conversions }
    }

    pub fn apply<'a>(&self, _input: &'a str) -> Cow<'a, str> {
        // en_US uses this for fancy apostrophe conversion.
        // TODO: See the ConvTable class in spylls.
        // We need the ability to move to the next unicode character in the
        // &str which I think we need to pull another crate in to do.
        unimplemented!()
    }
}

// TODO: Looks like this is only used by en_ZA. Is it worth the complexity?
// #[derive(Debug)]
// pub(crate) struct PhonetRule {
//     search: Regex,
//     replacement: String,
//     // TODO: enum?
//     start: bool,     // default false
//     end: bool,       // default false
//     priority: usize, // default 5
//     followup: bool,  // default true
// }
//
// impl PhonetRule {
//     pub fn r#match(&self, word: &str, pos: usize) -> bool {
//         if self.start && pos > 0 {
//             return false;
//         }
//         if self.end {
//             return self.search.is_match_at(word, pos);
//         }
//         // TODO: is_full_match_at
//         self.search.is_match_at(word, pos)
//     }
//
//     // TODO: translate parse_rule
// }

// #[derive(Debug)]
// pub(crate) struct PhonetTable {
//     rules: std::collections::HashMap<String, Vec<PhonetRule>>,
// }

#[cfg(test)]
mod test {
    use super::*;

    // We need a `&[&FlagSet]` to match `full_match` and `partial_match`'s
    // signatures.
    #[allow(clippy::vec_box)]
    fn compound_rule_guess(guess: &str) -> Vec<Box<FlagSet>> {
        let flag_type = FlagType::Short;
        let mut flag_sets = Vec::new();
        for ch in guess.chars() {
            let mut flag_set = FlagSet::new();
            flag_set.insert(flag_type.parse_flag_from_char(ch).unwrap());
            flag_sets.push(Box::new(flag_set));
        }
        flag_sets
    }

    fn compound_rule_pattern(pattern: &str) -> CompoundRule {
        CompoundRule::new(pattern, FlagType::Short).unwrap()
    }

    #[test]
    fn compound_rule_match_no_wildcards() {
        let pattern_ab = compound_rule_pattern("ab");
        let pattern_abc = compound_rule_pattern("abc");

        let guess_a = compound_rule_guess("a");
        let guess_a: Vec<_> = guess_a.iter().map(AsRef::as_ref).collect();

        let guess_ab = compound_rule_guess("ab");
        let guess_ab: Vec<_> = guess_ab.iter().map(AsRef::as_ref).collect();

        let guess_abc = compound_rule_guess("abc");
        let guess_abc: Vec<_> = guess_abc.iter().map(AsRef::as_ref).collect();

        assert!(pattern_ab.full_match(&guess_ab));
        assert!(pattern_ab.partial_match(&guess_abc));
        assert!(pattern_ab.partial_match(&guess_ab));
        assert!(pattern_ab.partial_match(&guess_a));

        assert!(pattern_abc.full_match(&guess_abc));
        assert!(pattern_abc.partial_match(&guess_abc));
        assert!(pattern_ab.partial_match(&guess_abc));
        assert!(pattern_ab.partial_match(&guess_ab));
        assert!(pattern_ab.partial_match(&guess_a));

        let guess_bc = compound_rule_guess("bc");
        let guess_bc: Vec<_> = guess_bc.iter().map(AsRef::as_ref).collect();

        assert!(!pattern_ab.full_match(&guess_bc));
        assert!(!pattern_ab.partial_match(&guess_bc));
        assert!(!pattern_abc.full_match(&guess_bc));
        assert!(!pattern_abc.partial_match(&guess_bc));
    }

    #[test]
    fn compound_rule_match_zero_or_one_wildcard() {
        let pattern = compound_rule_pattern("ab?c");

        let guess_ab = compound_rule_guess("ab");
        let guess_ab: Vec<_> = guess_ab.iter().map(AsRef::as_ref).collect();

        let guess_ac = compound_rule_guess("ac");
        let guess_ac: Vec<_> = guess_ac.iter().map(AsRef::as_ref).collect();

        let guess_abc = compound_rule_guess("abc");
        let guess_abc: Vec<_> = guess_abc.iter().map(AsRef::as_ref).collect();

        assert!(pattern.full_match(&guess_abc));
        assert!(pattern.partial_match(&guess_abc));
        assert!(pattern.full_match(&guess_ac));
        assert!(pattern.partial_match(&guess_ac));
        assert!(pattern.partial_match(&guess_ab));

        let guess_bc = compound_rule_guess("bc");
        let guess_bc: Vec<_> = guess_bc.iter().map(AsRef::as_ref).collect();
        assert!(!pattern.full_match(&guess_bc));
        assert!(!pattern.partial_match(&guess_bc));
    }

    #[test]
    fn compound_rule_match_zero_or_many_wildcard() {
        let pattern = compound_rule_pattern("ab*c");

        let guess_ac = compound_rule_guess("ac");
        let guess_ac: Vec<_> = guess_ac.iter().map(AsRef::as_ref).collect();

        let guess_abc = compound_rule_guess("abc");
        let guess_abc: Vec<_> = guess_abc.iter().map(AsRef::as_ref).collect();

        let guess_abbc = compound_rule_guess("abbc");
        let guess_abbc: Vec<_> = guess_abbc.iter().map(AsRef::as_ref).collect();

        let guess_abbbc = compound_rule_guess("abbbc");
        let guess_abbbc: Vec<_> = guess_abbbc.iter().map(AsRef::as_ref).collect();

        assert!(pattern.full_match(&guess_ac));
        assert!(pattern.partial_match(&guess_ac));

        assert!(pattern.full_match(&guess_abc));
        assert!(pattern.partial_match(&guess_abc));

        assert!(pattern.full_match(&guess_abbc));
        assert!(pattern.partial_match(&guess_abbc));

        assert!(pattern.full_match(&guess_abbbc));
        assert!(pattern.partial_match(&guess_abbbc));
    }
}
