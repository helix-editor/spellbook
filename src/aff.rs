//! Configuration and rulesets for a dictionary.
//! This comes from Hunspell `.aff` files, hence the name of the module & struct.

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    ops::Deref,
};

use regex::Regex;

use crate::{dic::Word, Flag, FlagSet};

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
    pub ignore_chars: String,
    /// Whether the language has sharps (ß)
    /// From the CHECKSHARPS command.
    pub check_sharps: bool,
    /// The flag marking words as forbidden so that they are rejected by check
    /// and suggest. This is necessary because some compounding and affix rules
    /// may produce a theoretically- but not actually correct word.
    /// From the FORBIDDENWORD command.
    pub forbidden_word_flag: Flag,
    /// Flag to mark words that shouldn't be considered correct unless their case
    /// matches the dictionary exactly.
    /// From the KEEPCASE command.
    pub keep_case_flag: Flag,

    // Suggestions
    /// Flag to mark a word of affix so that it is not produced by suggest.
    /// From the NOSUGGEST command.
    pub no_suggest_flag: Flag,
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
    pub prefixes: HashMap<Flag, Vec<Prefix>>,
    /// Dictionary of suffixes organized by flag.
    /// From the SFX command.
    pub suffixes: HashMap<Flag, Vec<Suffix>>,
    /// From the NEEDAFFIX command.
    pub need_affix_flag: Flag,
    /// From the CIRCUMFIX command.
    pub circumfix_flag: Flag,
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
    pub compound_flag: Flag,
    /// From the COMPOUNDBEGIN command.
    pub compound_begin_flag: Flag,
    /// From the COMPOUNDMIDDLE command.
    pub compound_middle_flag: Flag,
    /// From the COMPOUNDEND command.
    pub compound_end_flag: Flag,
    /// From the ONLYINCOMPOUND command.
    pub only_in_compound_flag: Flag,
    /// From the COMPOUNDPERMITFLAG command.
    pub compound_permit_flag: Flag,
    /// From the COMPOUNDFORBIDFLAG command.
    pub compound_forbid_flag: Flag,
    /// From the FORCEUCASE command.
    pub force_uppercase_flag: Flag,
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
    pub casing: Option<CustomCasing>,
    // TODO: suffixes/prefixes index in a trie?
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum CustomCasing {
    Germanic,
    Turkic,
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

    // pub fn parse_flags_from_chars(
    //     &self,
    //     mut chars: std::str::Chars,
    // ) -> Result<FlagSet, ParseFlagError> {
    //     use ParseFlagError::*;

    //     match self {
    //         Self::Long => {
    //             let mut flags = Vec::new();
    //             while let Some(c1) = chars.next() {
    //                 let c2 = match chars.next() {
    //                     Some(ch) => ch,
    //                     None => return Err(MissingSecondChar(c1)),
    //                 };
    //                 flags.push(u16::from_ne_bytes([c1 as u8, c2 as u8]) as Flag);
    //             }
    //             Ok(flags.into())
    //         }
    //         Self::Numeric => {
    //             let mut flags = Vec::new();
    //             let mut number = String::new();
    //             let mut separated = false;
    //             for ch in chars.by_ref() {
    //                 if ch.is_ascii_digit() {
    //                     number.push(ch);
    //                 } else if ch == ',' && separated {
    //                     return Err(DuplicateComma);
    //                 } else if ch == ',' {
    //                     separated = true;
    //                     let n = number.parse::<u16>().map_err(ParseIntError)?;
    //                     flags.push(n as Flag);
    //                 }
    //             }
    //             Ok(flags.into())
    //         }
    //         Self::Short | Self::Utf8 => {
    //             let flags = chars
    //                 .map(|ch| self.parse_flag_from_char(ch))
    //                 .collect::<Result<Vec<Flag>, _>>()?;
    //             Ok(flags.into())
    //         }
    //     }
    // }
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
    condition_regex: Regex,
    /// TODO
    replace_regex: Regex,
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

/// A set of formulas for combining words together via flags.
/// From the COMPOUNDRULE command.
#[derive(Debug)]
pub(crate) struct CompoundRule {
    pub flags: FlagSet,
    regex: Regex,
    partial_regex: Regex,
}

// TODO rename or merge into a larger error type.
pub(crate) enum CompoundRuleError {
    Flag(ParseFlagError),
    Regex(regex::Error),
}

impl From<regex::Error> for CompoundRuleError {
    fn from(err: regex::Error) -> Self {
        Self::Regex(err)
    }
}

impl From<ParseFlagError> for CompoundRuleError {
    fn from(err: ParseFlagError) -> Self {
        Self::Flag(err)
    }
}

impl CompoundRule {
    // TODO: Create a 'FlagPattern' which operates like a very simple
    // regex that matches on flags. Move the full_match and partial_match
    // logic into that type.
    pub fn new(text: &str, flag_type: FlagType) -> Result<Self, CompoundRuleError> {
        let (flags, parts) = if matches!(flag_type, FlagType::Long | FlagType::Numeric) {
            // Flags are surrounded by parentheses with these flag types, for example
            // (aa)(bb)*(cc) or (101)(102)*(103).
            // TODO lazy statics
            let flags: Vec<Flag> = Regex::new(r"\((.+?)\)")
                .unwrap()
                .find_iter(text)
                .map(|m| flag_type.parse_flag_from_str(m.as_str()))
                .collect::<Result<_, _>>()?;

            let parts: Vec<_> = Regex::new(r"\([^*?]+?\)[*?]?")
                .unwrap()
                .find_iter(text)
                .map(|part| Cow::from(part.as_str()))
                .collect();

            (flags, parts)
        } else {
            let flags: Vec<Flag> = text
                .chars()
                .map(|ch| flag_type.parse_flag_from_char(ch))
                .collect::<Result<_, _>>()?;

            let parts: Vec<_> = Regex::new(r"[^*?][*?]?")
                .unwrap()
                .find_iter(text)
                // `sv_*` dictionaries use `)` as flags. This is ad-hoc.
                .map(|part| Cow::from(part.as_str().replace(')', "\\)")))
                .collect();

            (flags, parts)
        };

        let regex = Regex::new(&parts.join(""))?;
        let partial_regex_string = parts
            .iter()
            .rfold(String::new(), |acc, part| format!("{part}({acc})?"));
        let partial_regex = Regex::new(&partial_regex_string)?;

        Ok(Self {
            flags: flags.into(),
            regex,
            partial_regex,
        })
    }

    // That type only needs to care about '*' and '?' rules.
    pub fn full_match(&self, _flag_sets: &[FlagSet]) -> bool {
        unimplemented!()
    }

    pub fn partial_match(&self, flag_sets: &[FlagSet]) -> bool {
        unimplemented!()
    }

    // fn cartesian_product<'a, T: Copy>(vec: &'a Vec<T>) -> impl Iterator<Item = (T, T)> + 'a {
    //     vec.iter().flat_map(|x| vec.iter().map(move |y| (*x, *y)))
    // }
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
    pub fn new(left: &str, right: &str) -> Self {
        unimplemented!()
    }

    pub fn r#match(&self, left: AffixForm, right: AffixForm) -> bool {
        fn is_none_or<T, F>(opt: Option<T>, f: F) -> bool
        where
            F: FnOnce(T) -> bool,
        {
            match opt {
                Some(val) => f(val),
                None => true,
            }
        }

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

/// A hypothesis of how some word might be split into stem, suffix(es)
/// and prefix(es).
#[derive(Debug)]
// TODO: move this to a lookup module? Move everything to a types module?
pub(crate) struct AffixForm {
    text: String,
    stem: String,
    prefixes: [Option<Prefix>; 2],
    suffixes: [Option<Suffix>; 2],
    in_dictionary: Option<Word>,
}

impl AffixForm {
    pub fn has_affixes(&self) -> bool {
        self.prefixes[0].is_some() || self.suffixes[0].is_some()
    }

    pub fn is_base(&self) -> bool {
        !self.has_affixes()
    }

    pub fn flags(&self) -> FlagSet {
        let mut flags = Vec::new();
        if let Some(word) = &self.in_dictionary {
            flags.extend(word.flags.deref());
        }
        if let Some(prefix) = &self.prefixes[0] {
            flags.extend(prefix.flags.deref());
        }
        if let Some(suffix) = &self.suffixes[0] {
            flags.extend(suffix.flags.deref());
        }
        flags.into()
    }
}

/// Table of conversions that should be applied before or after processing.
/// processing.
///
/// This is currently simplified to ignore patterns that show up only in Hunspells
/// test harness but not in actual dictionaries.
///
/// From ICONV and/or OCONV.
#[derive(Debug)]
pub(crate) struct ConversionTable {
    conversions: Vec<(String, String)>,
}

impl ConversionTable {
    pub fn new(conversions: &[(&str, &str)]) -> Self {
        let conversions: Vec<_> = conversions
            .iter()
            .map(|(pattern, replacement)| (pattern.to_string(), replacement.to_string()))
            .collect();
        Self { conversions }
    }

    pub fn apply(&self, input: &str) -> String {
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
