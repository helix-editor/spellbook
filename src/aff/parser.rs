//! The parser for `.aff` and `.dic` files.
//!
//! This parser takes inspiration from Zspell: <https://github.com/pluots/zspell/blob/71ae77932f2cc67f593d846a26a9ffd7cf6d0412/crates/zspell/src/parser_affix.rs>
//! and Nuspell. The Rust bits are mostly Zspell: folding over a const slice of parser functions.
//! Rather than trying to parse directly into the `Aff_Data` type, Nuspell has a sort of
//! scratch-pad data structure for the initial parsing. This works well for types like
//! `AffixIndex` which are most efficient to build all-at-once from all elements rather than
//! constructively by inserting each element.

use core::{
    fmt,
    hash::BuildHasher,
    iter::{Enumerate, Peekable, TakeWhile},
    str::{Chars, FromStr, SplitWhitespace},
};

use hashbrown::HashMap;

use crate::{
    alloc::{
        string::{String, ToString},
        vec::Vec,
    },
    WordList,
};

use crate::{Flag, FlagSet};

use super::{AffData, AffOptions, CompoundRule, Condition, FlagType, Prefix, Suffix};

type Result<T> = core::result::Result<T, ParseDictionaryError>;
type ParseResult = Result<()>;

#[derive(Debug, Default)]
struct AffLineParser<'aff> {
    options: AffOptions,
    // options only used for parsing:
    flag_type: FlagType,
    // encoding: Encoding,
    flag_aliases: Vec<FlagSet>,
    // wordchars: String, deprecated?
    replacements: Vec<(&'aff str, &'aff str)>,
    break_patterns: Vec<&'aff str>,
    compound_syllable_vowels: &'aff str,
    ignore_chars: &'aff str,
    try_chars: &'aff str,
    keyboard_closeness: &'aff str,
    prefixes: Vec<Prefix>,
    suffixes: Vec<Suffix>,
    compound_rules: Vec<CompoundRule>,
}

type Parser = for<'aff> fn(&mut AffLineParser<'aff>, &mut Lines<'aff>) -> ParseResult;

// These parsers are only used for the `.aff` file's contents. The `.dic` file is handled ad-hoc.
const AFF_PARSERS: [(&str, Parser); 45] = [
    ("FLAG", parse_flag_type),
    // Flags
    ("FORBIDDENWORD", parse_forbidden_word_flag),
    ("CIRCUMFIX", parse_circumfix_flag),
    ("KEEPCASE", parse_keep_case_flag),
    ("NEEDAFFIX", parse_need_affix_flag),
    ("NOSUGGEST", parse_no_suggest_flag),
    ("SUBSTANDARD", parse_substandard_flag),
    ("WARN", parse_warn_flag),
    ("COMPOUNDFLAG", parse_compound_flag),
    ("COMPOUNDBEGIN", parse_compound_begin_flag),
    ("COMPOUNDMIDDLE", parse_compound_middle_flag),
    ("COMPOUNDLAST", parse_compound_last_flag),
    ("ONLYINCOMPOUND", parse_only_in_compound_flag),
    ("COMPOUNDPERMITFLAG", parse_compound_permit_flag),
    ("COMPOUNDFORBIDFLAG", parse_compound_forbid_flag),
    ("FORCEUCASE", parse_compound_force_uppercase_flag),
    // Bools
    ("COMPLEXPREFIXES", parse_complex_prefixes),
    ("FULLSTRIP", parse_fullstrip),
    ("CHECKSHARPS", parse_checksharps),
    ("FORBIDWARN", parse_forbid_warn),
    ("COMPOUNDMORESUFFIXES", parse_compound_more_suffixes),
    ("CHECKCOMPOUNDDUP", parse_compound_check_duplicate),
    ("CHECKCOMPOUNDREP", parse_compound_check_rep),
    ("CHECKCOMPOUNDCASE", parse_compound_check_case),
    ("CHECKCOMPOUNDTRIPLE", parse_compound_check_triple),
    ("SIMPLIFIEDTRIPLE", parse_compound_simplified_triple),
    ("SYLLABLENUM", parse_compound_syllable_num),
    ("ONLYMAXDIFF", parse_only_max_diff),
    ("NOSPLITSUGS", parse_no_split_suggestions),
    ("SUGSWITHDOTS", parse_suggest_with_dots),
    // "Shorts" as Nuspell calls them (u16s in Spellbook)
    ("COMPOUNDMIN", parse_compound_min_length),
    ("COMPOUNDWORDMAX", parse_compound_max_word_count),
    ("MAXCPDSUGS", parse_max_compound_suggestions),
    ("MAXNGRAMSUGS", parse_max_ngram_suggestions),
    ("MAXDIFF", parse_max_diff_factor),
    // Strings
    ("IGNORE", parse_ignore_chars),
    ("KEY", parse_keyboard_closeness),
    ("TRY", parse_try_chars),
    // String pairs
    // TODO: phonetic replacements, input & output conversion
    ("REP", parse_replacements),
    // Remaining complicated structures
    ("BREAK", parse_break_patterns),
    ("COMPOUNDSYLLABLE", parse_compound_syllable),
    ("AF", parse_flag_aliases),
    ("PFX", parse_prefix_table),
    ("SFX", parse_suffix_table),
    ("COMPOUNDRULE", parse_compound_rule_table),
    // TODO:
    // ("CHECKCOMPOUNDPATTERN", parse_compound_pattern),
];

// TODO: encoding? Or just require all dictionaries to be UTF-8?
pub(crate) fn parse<'dic, 'aff, S: BuildHasher + Clone>(
    dic_text: &'dic str,
    aff_text: &'aff str,
    build_hasher: S,
) -> Result<AffData<S>> {
    // First parse the aff file.
    let mut lines = Lines::<'aff>::new(aff_text, ParseDictionaryErrorSource::Aff);
    let mut aff_parsers =
        HashMap::with_capacity_and_hasher(AFF_PARSERS.len(), build_hasher.clone());
    aff_parsers.extend(AFF_PARSERS);
    let mut cx = AffLineParser::<'aff>::default();

    while !lines.is_finished() {
        if let Some(parser) = lines.next_word().and_then(|key| aff_parsers.get(key)) {
            (parser)(&mut cx, &mut lines)?;
        }

        lines.advance_line()
    }

    // Then parse the dic file into a WordList.
    let mut lines = Lines::<'dic>::new(dic_text, ParseDictionaryErrorSource::Dic);
    let row_count = lines
        .take_exactly_one_word()?
        .parse::<usize>()
        .map_err(|err| lines.error(ParseDictionaryErrorKind::MalformedNumber(err)))?;
    let mut words = WordList::with_capacity_and_hasher(row_count, build_hasher);

    for row in 1..=row_count {
        lines.advance_line();
        if lines.is_finished() {
            return Err(lines.error(ParseDictionaryErrorKind::MismatchedRowCount {
                expected: row_count,
                actual: row,
            }));
        }

        // NOTE: currently we ignore morphological fields.
        let word = match lines.next_word() {
            Some(word) => word,
            // Empty lines are skipped.
            None => continue,
        };
        let (word, flagset) = parse_dic_line(word, cx.flag_type, &cx.flag_aliases, cx.ignore_chars)
            .map_err(|err| lines.error(ParseDictionaryErrorKind::MalformedFlag(err)))?;
        words.insert(word, flagset);
    }

    // Collect everything into AffData.
    Ok(AffData {
        words,
        prefixes: cx.prefixes.into(),
        suffixes: cx.suffixes.into(),
        break_table: cx.break_patterns.into(),
        compound_rules: cx.compound_rules.into(),
        compound_syllable_vowels: cx.compound_syllable_vowels.to_string(),
        // compound_patterns: todo!(),
        ignore_chars: cx.ignore_chars.to_string(),
        keyboard_closeness: cx.keyboard_closeness.to_string(),
        try_chars: cx.try_chars.to_string(),
        options: cx.options,
    })
}

fn parse_flag_type(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    let word = lines.take_exactly_one_word()?;

    word.parse::<FlagType>()
        .map(|flag_type| cx.flag_type = flag_type)
        .map_err(|err| lines.error(ParseDictionaryErrorKind::UnknownFlagType(err)))
}

fn parse_forbidden_word_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.forbidden_word_flag = Some(flag))
}

fn parse_circumfix_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.circumfix_flag = Some(flag))
}

fn parse_keep_case_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.keep_case_flag = Some(flag))
}

fn parse_need_affix_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.need_affix_flag = Some(flag))
}

fn parse_no_suggest_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.no_suggest_flag = Some(flag))
}

fn parse_substandard_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.substandard_flag = Some(flag))
}

fn parse_warn_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.warn_flag = Some(flag))
}

fn parse_compound_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_flag = Some(flag))
}

fn parse_compound_begin_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_begin_flag = Some(flag))
}

fn parse_compound_middle_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_middle_flag = Some(flag))
}

fn parse_compound_last_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_last_flag = Some(flag))
}

fn parse_only_in_compound_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.only_in_compound_flag = Some(flag))
}

fn parse_compound_permit_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_permit_flag = Some(flag))
}

fn parse_compound_forbid_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_forbid_flag = Some(flag))
}

fn parse_compound_force_uppercase_flag(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_flag(cx)
        .map(|flag| cx.options.compound_force_uppercase_flag = Some(flag))
}

fn parse_complex_prefixes(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.complex_prefixes = b)
}

fn parse_fullstrip(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.fullstrip = b)
}

fn parse_checksharps(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.checksharps = b)
}

fn parse_forbid_warn(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.forbid_warn = b)
}

fn parse_compound_more_suffixes(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_more_suffixes = b)
}

fn parse_compound_check_duplicate(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_check_duplicate = b)
}

fn parse_compound_check_rep(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_check_rep = b)
}

fn parse_compound_check_case(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_check_case = b)
}

fn parse_compound_check_triple(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_check_triple = b)
}

fn parse_compound_simplified_triple(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_simplified_triple = b)
}

fn parse_compound_syllable_num(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.compound_syllable_num = b)
}

fn parse_only_max_diff(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.only_max_diff = b)
}

fn parse_no_split_suggestions(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_bool()
        .map(|b| cx.options.no_split_suggestions = b)
}

fn parse_suggest_with_dots(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_bool().map(|b| cx.options.suggest_with_dots = b)
}

fn parse_compound_min_length(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_short()
        .map(|s| cx.options.compound_min_length = s.min(1))
}

fn parse_compound_max_word_count(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_short()
        .map(|s| cx.options.compound_max_word_count = s)
}

fn parse_max_compound_suggestions(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_short()
        .map(|s| cx.options.max_compound_suggestions = s)
}

fn parse_max_ngram_suggestions(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines
        .parse_short()
        .map(|s| cx.options.max_ngram_suggestions = s)
}

fn parse_max_diff_factor(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    let s = lines.parse_short()?;
    cx.options.max_diff_factor = if s > 10 { 5 } else { s };
    Ok(())
}

fn parse_ignore_chars<'a>(cx: &mut AffLineParser<'a>, lines: &mut Lines<'a>) -> ParseResult {
    lines
        .take_exactly_one_word()
        .map(|word| cx.ignore_chars = word)
}

fn parse_keyboard_closeness<'a>(cx: &mut AffLineParser<'a>, lines: &mut Lines<'a>) -> ParseResult {
    lines
        .take_exactly_one_word()
        .map(|word| cx.keyboard_closeness = word)
}

fn parse_try_chars<'a>(cx: &mut AffLineParser<'a>, lines: &mut Lines<'a>) -> ParseResult {
    lines
        .take_exactly_one_word()
        .map(|word| cx.try_chars = word)
}

fn parse_replacements<'aff>(cx: &mut AffLineParser<'aff>, lines: &mut Lines<'aff>) -> ParseResult {
    lines.parse_table2("REP", |str1, str2| {
        cx.replacements.push((str1, str2));
        Ok(())
    })
}

fn parse_break_patterns<'aff>(
    cx: &mut AffLineParser<'aff>,
    lines: &mut Lines<'aff>,
) -> ParseResult {
    lines.parse_table1("BREAK", |str| {
        cx.break_patterns.push(str);
        Ok(())
    })
}

fn parse_compound_syllable<'aff>(
    cx: &mut AffLineParser<'aff>,
    lines: &mut Lines<'aff>,
) -> ParseResult {
    // Takes the shape COMPOUNDSYLLABLE <compound_syllable_max> <compound_syllable_vowels>
    let mut words = match lines.words.take() {
        Some(words) => words,
        None => {
            return Err(lines.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 2,
                actual: 0,
            }))
        }
    };

    let max = match words.next() {
        Some(word) => word,
        None => {
            return Err(lines.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 2,
                actual: 0,
            }))
        }
    };
    let vowels = match words.next() {
        Some(word) => word,
        None => {
            return Err(lines.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 2,
                actual: 1,
            }))
        }
    };
    let remaining_words = words.count();
    if remaining_words > 0 {
        return Err(lines.error(ParseDictionaryErrorKind::MismatchedArity {
            expected: 2,
            actual: 2 + remaining_words,
        }));
    }

    cx.options.compound_syllable_max = max
        .parse::<u16>()
        .map_err(|err| lines.error(ParseDictionaryErrorKind::MalformedNumber(err)))?;
    cx.compound_syllable_vowels = vowels;

    Ok(())
}

fn parse_flag_aliases(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_table1("AF", |alias| {
        let flagset = parse_flags_from_chars(cx.flag_type, alias.chars())?;
        cx.flag_aliases.push(flagset);
        Ok(())
    })
}

fn parse_prefix_table(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_affix_table(
        "PFX",
        cx.flag_type,
        |flag, crossproduct, strip, add, condition, flagset_str| {
            let flagset = decode_flagset(flagset_str, cx.flag_type, &cx.flag_aliases)?;
            let prefix = Prefix::new(flag, crossproduct, strip, add, condition, flagset)?;
            cx.prefixes.push(prefix);
            Ok(())
        },
    )
}

fn parse_suffix_table(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_affix_table(
        "SFX",
        cx.flag_type,
        |flag, crossproduct, strip, add, condition, flagset_str| {
            let flagset = decode_flagset(flagset_str, cx.flag_type, &cx.flag_aliases)?;
            let suffix = Suffix::new(flag, crossproduct, strip, add, condition, flagset)?;
            cx.suffixes.push(suffix);
            Ok(())
        },
    )
}

fn parse_compound_rule_table(cx: &mut AffLineParser, lines: &mut Lines) -> ParseResult {
    lines.parse_table1("COMPOUNDRULE", |word| {
        let rule = parse_compound_rule(word, cx.flag_type)?;
        cx.compound_rules.push(rule);
        Ok(())
    })
}

/// A helper type that means "words on a line split by whitespace with comments
/// dropped." This is a concretion of `impl Iterator<Item = &'a str>`.
type Words<'text> = TakeWhile<SplitWhitespace<'text>, for<'b, 'c> fn(&'b &'c str) -> bool>;

struct Lines<'text> {
    lines: Peekable<Enumerate<core::str::Lines<'text>>>,
    words: Option<Words<'text>>,
    source: ParseDictionaryErrorSource,
}

impl<'text> Lines<'text> {
    fn new(text: &'text str, source: ParseDictionaryErrorSource) -> Self {
        let mut lines = text.lines().enumerate().peekable();
        let words = lines.peek().map(|(_line_no, line)| {
            line.split_whitespace()
                .take_while((|word| !word.starts_with('#')) as for<'b, 'c> fn(&'b &'c str) -> bool)
        });

        Self {
            lines,
            words,
            source,
        }
    }

    fn is_finished(&mut self) -> bool {
        self.lines.peek().is_none()
    }

    fn advance_line(&mut self) {
        self.lines.next();
        self.words = self.lines.peek().map(|(_line_no, line)| {
            line.split_whitespace()
                .take_while((|word| !word.starts_with('#')) as for<'b, 'c> fn(&'b &'c str) -> bool)
        });
    }

    fn next_word(&mut self) -> Option<&str> {
        let mut words = self.words.take()?;
        let word = words.next()?;
        self.words = Some(words);
        Some(word)
    }

    fn take_exactly_one_word(&mut self) -> Result<&'text str> {
        let mut words = self.words.take().ok_or_else(|| {
            self.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 1,
                actual: 0,
            })
        })?;
        let word = words.next().ok_or_else(|| {
            self.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 1,
                actual: 0,
            })
        })?;
        self.words = Some(words);
        Ok(word)
    }

    fn parse_flag(&mut self, cx: &AffLineParser) -> Result<Flag> {
        let word = self.take_exactly_one_word()?;
        parse_flag_from_str(cx.flag_type, word)
            .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedFlag(err)))
    }

    fn parse_bool(&mut self) -> Result<bool> {
        // Boolean flags are specified by just the key. For example if you see `COMPLEXPREFIXES`
        // as a line, `complex_prefixes` is true. Otherwise it's false.
        let count = self
            .words
            .take()
            .map(|words| words.count())
            .unwrap_or_default();
        if count > 0 {
            return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 0,
                actual: count,
            }));
        }
        Ok(true)
    }

    fn parse_short(&mut self) -> Result<u16> {
        let word = self.take_exactly_one_word()?;
        word.parse::<u16>()
            .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))
    }

    fn parse_table1<F>(&mut self, key: &str, mut f: F) -> ParseResult
    where
        F: FnMut(&'text str) -> core::result::Result<(), ParseDictionaryErrorKind>,
    {
        let row_count = self
            .take_exactly_one_word()?
            .parse::<usize>()
            .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?;

        for row in 1..=row_count {
            self.advance_line();
            if self.is_finished() || self.next_word() != Some(key) {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                    expected: row_count,
                    actual: row,
                }));
            }

            let mut words = match self.words.take() {
                Some(words) => words,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 1,
                        actual: 0,
                    }))
                }
            };

            let word = match words.next() {
                Some(word) => word,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 1,
                        actual: 0,
                    }))
                }
            };
            let remaining_words = words.count();
            if remaining_words > 0 {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 1,
                    actual: 1 + remaining_words,
                }));
            }

            f(word).map_err(|kind| self.error(kind))?;
        }

        Ok(())
    }

    fn parse_table2<F>(&mut self, key: &str, mut f: F) -> ParseResult
    where
        F: FnMut(&'text str, &'text str) -> core::result::Result<(), ParseDictionaryErrorKind>,
    {
        let row_count = self
            .take_exactly_one_word()?
            .parse::<usize>()
            .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?;

        for row in 1..=row_count {
            self.advance_line();
            if self.is_finished() || self.next_word() != Some(key) {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                    expected: row_count,
                    actual: row,
                }));
            }

            let mut words = match self.words.take() {
                Some(words) => words,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 2,
                        actual: 0,
                    }))
                }
            };

            let word1 = match words.next() {
                Some(word) => word,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 2,
                        actual: 0,
                    }))
                }
            };
            let word2 = match words.next() {
                Some(word) => word,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 2,
                        actual: 1,
                    }))
                }
            };
            let remaining_words = words.count();
            if remaining_words > 0 {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 2,
                    actual: 2 + remaining_words,
                }));
            }

            f(word1, word2).map_err(|kind| self.error(kind))?;
        }

        Ok(())
    }

    fn parse_affix_table<F>(&mut self, key: &str, flag_type: FlagType, mut f: F) -> ParseResult
    where
        F: FnMut(
            Flag,         // flag
            bool,         // crossproduct
            Option<&str>, // strip
            &str,         // add
            Option<&str>, // condition
            &str,         // flagset
        ) -> core::result::Result<(), ParseDictionaryErrorKind>,
    {
        // Header takes the shapes:
        // PFX flag cross_product row_count
        // SFX flag cross_product row_count
        let mut words = match self.words.take() {
            Some(words) => words,
            None => {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 3,
                    actual: 0,
                }))
            }
        };

        let flag_str = match words.next() {
            Some(word) => word,
            None => {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 3,
                    actual: 0,
                }))
            }
        };
        let flag = parse_flag_from_str(flag_type, flag_str)
            .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedFlag(err)))?;

        let crossproduct = match words.next() {
            Some("Y") => true,
            Some("N") => true,
            Some(_) => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
            None => {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 3,
                    actual: 1,
                }))
            }
        };

        let row_count = match words.next() {
            Some(word) => word
                .parse::<usize>()
                .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?,
            None => {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 3,
                    actual: 2,
                }))
            }
        };

        let remaining_words = words.count();
        if remaining_words > 0 {
            return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 3,
                actual: 3 + remaining_words,
            }));
        }

        for row in 1..=row_count {
            // Each row takes the shape:
            // PFX flag stripping prefix [condition [morphological_fields...]]
            // SFX flag stripping suffix [condition [morphological_fields...]]
            self.advance_line();
            if self.is_finished() || self.next_word() != Some(key) {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                    expected: row_count,
                    actual: row,
                }));
            }

            let mut words = match self.words.take() {
                Some(words) => words,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 3,
                        actual: 0,
                    }))
                }
            };

            if words.next() != Some(flag_str) {
                return Err(self.error(ParseDictionaryErrorKind::MalformedAffix));
            }

            let strip = match words.next() {
                Some("0") => None,
                Some(word) => Some(word),
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 3,
                        actual: 1,
                    }))
                }
            };

            // the add needs to be split into flagset.
            let (add, flagset) = match words.next() {
                Some(word) => split_word_and_flagset_naive(word),
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                        expected: 3,
                        actual: 2,
                    }))
                }
            };

            // "." is the empty condition - it always matches. We'll use an Option for this
            // fast lane instead.
            let condition = words.next().filter(|&cond| cond != ".");

            // NOTE: we don't check the remaining words on the line because morphological fields
            // are allowed after the condition and we don't currently parse those.

            f(flag, crossproduct, strip, add, condition, flagset)
                .map_err(|kind| self.error(kind))?
        }

        Ok(())
    }

    fn error(&mut self, kind: ParseDictionaryErrorKind) -> ParseDictionaryError {
        ParseDictionaryError {
            kind,
            source: self.source,
            line_number: self
                .lines
                .peek()
                .map(|(line_number, _line)| line_number)
                .copied(),
        }
    }
}

fn try_flag_from_u16(val: u16) -> core::result::Result<Flag, ParseFlagError> {
    Flag::new(val).ok_or(ParseFlagError::ZeroFlag)
}

fn try_flag_from_u32(val: u32) -> core::result::Result<Flag, ParseFlagError> {
    if val > u16::MAX as u32 {
        return Err(ParseFlagError::FlagAbove65535);
    }
    try_flag_from_u16(val as u16)
}

fn try_flag_from_char(ch: char) -> core::result::Result<Flag, ParseFlagError> {
    try_flag_from_u32(ch as u32)
}

fn parse_flag_from_str(
    flag_type: FlagType,
    input: &str,
) -> core::result::Result<Flag, ParseFlagError> {
    use ParseFlagError::*;
    assert!(!input.is_empty());

    match flag_type {
        FlagType::Short => {
            let mut chars = input.chars();
            let ch = chars.next().expect("asserted to be non-empty above");
            if ch.is_ascii() {
                // The flag is ASCII: it's a valid `u8` so it can fit into a `u16`.
                try_flag_from_u16(ch as u16)
            } else {
                Err(NonAscii(ch))
            }
        }
        FlagType::Long => {
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
        FlagType::Numeric => {
            let number = input.parse::<u16>().map_err(ParseIntError)?;
            try_flag_from_u16(number)
        }
        FlagType::Utf8 => {
            let mut chars = input.chars();
            let ch = chars.next().expect("asserted to be non-empty above");
            try_flag_from_char(ch)
        }
    }
}

fn parse_flags_from_chars(
    flag_type: FlagType,
    mut chars: Chars,
) -> core::result::Result<FlagSet, ParseFlagError> {
    use ParseFlagError::*;

    match flag_type {
        FlagType::Short => {
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
        FlagType::Long => {
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
        FlagType::Numeric => {
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
            if !number.is_empty() {
                let n = number.parse::<u16>().map_err(ParseIntError)?;
                flags.insert(try_flag_from_u16(n)?);
            }
            Ok(flags)
        }
        FlagType::Utf8 => chars.map(try_flag_from_char).collect(),
    }
}

/// Input is assumed to be a single word, i.e. not containing whitespace.
/// This only splits on the slash, it doesn't handle escaping.
// NOTE: in pratice no dictionary uses escaping for affix continuation flags.
fn split_word_and_flagset_naive(input: &str) -> (&str, &str) {
    input.split_once('/').unwrap_or((input, ""))
}

/// Attempt to look up the flagset as an alias.
fn decode_flagset(
    input: &str,
    flag_type: FlagType,
    aliases: &[FlagSet],
) -> core::result::Result<FlagSet, ParseFlagError> {
    // Fast lane for numeric flag-types and empty aliases.
    if matches!(flag_type, FlagType::Numeric) || aliases.is_empty() {
        // TODO: refactor this function to take a str
        return parse_flags_from_chars(flag_type, input.chars());
    }

    if let Some(index) = input
        .parse::<u16>()
        .ok()
        .map(|i| i as usize)
        .filter(|&i| i > 0 && i <= aliases.len())
    {
        // NOTE: the aliases are 1-indexed.
        Ok(aliases[index - 1].clone())
    } else {
        parse_flags_from_chars(flag_type, input.chars())
    }
}

fn parse_dic_line(
    input: &str,
    flag_type: FlagType,
    aliases: &[FlagSet],
    ignore_chars: &str,
) -> core::result::Result<(String, FlagSet), ParseFlagError> {
    let mut chars = input.chars();
    let mut word = String::new();
    let mut escape = false;
    for ch in chars.by_ref() {
        match ch {
            '\\' => escape = !escape,
            '/' if !escape => break,
            _ => word.push(ch),
        }
    }
    if !ignore_chars.is_empty() {
        todo!("erase ignored characters from the word")
    }
    let flags_str: String = chars.collect();
    let flag_set = decode_flagset(&flags_str, flag_type, aliases)?;

    Ok((word, flag_set))
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseCompoundRuleError {
    ParseFlagError(ParseFlagError),
    InvalidFormat,
}

impl core::fmt::Display for ParseCompoundRuleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ParseFlagError(err) => write!(f, "failed to parse flag: {}", err),
            Self::InvalidFormat => f.write_str("invalid compound rule format"),
        }
    }
}

impl From<ParseFlagError> for ParseCompoundRuleError {
    fn from(err: ParseFlagError) -> Self {
        Self::ParseFlagError(err)
    }
}

impl From<ParseCompoundRuleError> for ParseDictionaryErrorKind {
    fn from(err: ParseCompoundRuleError) -> Self {
        Self::MalformedCompoundRule(err)
    }
}

fn parse_compound_rule(
    input: &str,
    flag_type: FlagType,
) -> core::result::Result<CompoundRule, ParseCompoundRuleError> {
    use super::CompoundRuleElement as Elem;

    let rough_capacity = if matches!(flag_type, FlagType::Long) {
        input.len() / 2
    } else {
        input.len()
    };
    let mut rule = Vec::with_capacity(rough_capacity);

    match flag_type {
        FlagType::Short => {
            for ch in input.chars() {
                if !ch.is_ascii() {
                    return Err(ParseFlagError::NonAscii(ch).into());
                }
                let element = match ch {
                    // Can't start with a wildcard.
                    '*' | '?' if rule.is_empty() => {
                        return Err(ParseCompoundRuleError::InvalidFormat);
                    }
                    '*' => Elem::ZeroOrMore,
                    '?' => Elem::ZeroOrOne,
                    _ => Elem::Flag(try_flag_from_char(ch)?),
                };
                rule.push(element);
            }
        }
        FlagType::Utf8 => {
            for ch in input.chars() {
                let element = match ch {
                    // Can't start with a wildcard.
                    '*' | '?' if rule.is_empty() => {
                        return Err(ParseCompoundRuleError::InvalidFormat);
                    }
                    '*' => Elem::ZeroOrMore,
                    '?' => Elem::ZeroOrOne,
                    _ => Elem::Flag(try_flag_from_char(ch)?),
                };
                rule.push(element);
            }
        }
        FlagType::Long => {
            let mut chars = input.chars().peekable();

            loop {
                match chars.next() {
                    Some('(') => {
                        let c1 = match chars.next() {
                            Some(ch) if !ch.is_ascii() => {
                                return Err(ParseFlagError::NonAscii(ch).into())
                            }
                            Some(ch) if ch != ')' => ch,
                            _ => return Err(ParseCompoundRuleError::InvalidFormat),
                        };
                        let c2 = match chars.next() {
                            Some(ch) if !ch.is_ascii() => {
                                return Err(ParseFlagError::NonAscii(ch).into())
                            }
                            Some(ch) if ch != ')' => ch,
                            _ => return Err(ParseCompoundRuleError::InvalidFormat),
                        };

                        if chars.next() != Some(')') {
                            return Err(ParseCompoundRuleError::InvalidFormat);
                        }

                        let flag = try_flag_from_u16(u16::from_ne_bytes([c1 as u8, c2 as u8]))?;
                        rule.push(Elem::Flag(flag));
                    }
                    Some(_) => return Err(ParseCompoundRuleError::InvalidFormat),
                    None => break,
                }

                match chars.peek() {
                    Some('*') => {
                        rule.push(Elem::ZeroOrMore);
                        chars.next();
                    }
                    Some('?') => {
                        rule.push(Elem::ZeroOrOne);
                        chars.next();
                    }
                    _ => (),
                }
            }
        }
        FlagType::Numeric => {
            // Most dictionaries will not exceed 3 digit numeric flags.
            let mut number = String::with_capacity(3);
            let mut chars = input.chars().peekable();

            loop {
                match chars.next() {
                    Some('(') => {
                        loop {
                            match chars.next() {
                                Some(ch) if ch.is_ascii_digit() => number.push(ch),
                                Some(')') if !number.is_empty() => break,
                                _ => return Err(ParseCompoundRuleError::InvalidFormat),
                            }
                        }

                        let n = number
                            .parse::<u16>()
                            .map_err(ParseFlagError::ParseIntError)?;
                        number.clear();

                        let flag = try_flag_from_u16(n)?;
                        rule.push(Elem::Flag(flag));
                    }
                    Some(_) => return Err(ParseCompoundRuleError::InvalidFormat),
                    None => break,
                }

                match chars.peek() {
                    Some('*') => {
                        rule.push(Elem::ZeroOrMore);
                        chars.next();
                    }
                    Some('?') => {
                        rule.push(Elem::ZeroOrOne);
                        chars.next();
                    }
                    _ => (),
                }
            }
        }
    }

    Ok(rule)
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseDictionaryErrorKind {
    UnknownFlagType(UnknownFlagTypeError),
    MalformedFlag(ParseFlagError),
    MalformedNumber(core::num::ParseIntError),
    UnexpectedNonWhitespace(char),
    MismatchedArity { expected: usize, actual: usize },
    MismatchedRowCount { expected: usize, actual: usize },
    MalformedCompoundRule(ParseCompoundRuleError),
    // MalformedMorphologicalField(String),
    MalformedAffix,
    MalformedCondition(ConditionError),
    Empty,
}

impl From<UnknownFlagTypeError> for ParseDictionaryErrorKind {
    fn from(err: UnknownFlagTypeError) -> Self {
        Self::UnknownFlagType(err)
    }
}

impl From<ParseFlagError> for ParseDictionaryErrorKind {
    fn from(err: ParseFlagError) -> Self {
        Self::MalformedFlag(err)
    }
}

impl From<ConditionError> for ParseDictionaryErrorKind {
    fn from(err: ConditionError) -> Self {
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
            Self::MalformedCompoundRule(err) => {
                write!(f, "compound rule is malformed: {}", err)
            }
            // Self::MalformedMorphologicalField(s) => {
            //     write!(f, "morphological field '{}' is malformed", s)
            // }
            Self::MalformedAffix => write!(f, "failed to parse affix"),
            Self::MalformedCondition(err) => write!(f, "condition is malformed: {}", err),
            Self::Empty => write!(f, "the file is empty"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnknownFlagTypeError(String);

impl FromStr for FlagType {
    type Err = UnknownFlagTypeError;

    fn from_str(s: &str) -> core::result::Result<Self, Self::Err> {
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

#[derive(Debug, PartialEq, Eq, Clone)]
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

/// An error arising from validating a [`Condition`].
///
/// Conditions are a subset of regular expressions that include positive and negative character
/// classes and the wildcard character. A condition might fail validation if the character classes
/// are open (for example `foo]` or `foo[bar`) or if the condition has an empty character class,
/// which is not valid (`[]`).
// Hands where I can see 'em, clippy. The only time I ever went down was when a machine was easing
// at the wrong time.
#[allow(clippy::enum_variant_names)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

    fn from_str(s: &str) -> core::result::Result<Self, Self::Err> {
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

#[cfg(test)]
mod test {
    use crate::{alloc::vec, flag, flagset};

    use super::*;

    #[test]
    fn naive_word_flagset_split_test() {
        assert_eq!(
            ("word", "flags"),
            split_word_and_flagset_naive("word/flags")
        );
        assert_eq!(("word", ""), split_word_and_flagset_naive("word"));
        assert_eq!(("", ""), split_word_and_flagset_naive(""));
    }

    #[test]
    fn parse_flagset_test() {
        assert_eq!(
            Ok(flag!('a' as u16)),
            parse_flag_from_str(FlagType::Short, "a")
        );
        assert_eq!(Ok(flag!(1)), parse_flag_from_str(FlagType::Numeric, "1"));

        assert_eq!(
            Ok(flagset![1]),
            parse_flags_from_chars(FlagType::Numeric, "1".chars())
        );
    }

    #[test]
    fn decode_flagset_test() {
        let aliases = &[flagset![1], flagset![2], flagset![3, 4]];

        // NOTE: 1-indexing.
        assert_eq!(
            flagset![1],
            decode_flagset("1", FlagType::default(), aliases).unwrap()
        );
        assert_eq!(
            flagset![2],
            decode_flagset("2", FlagType::default(), aliases).unwrap()
        );
        assert_eq!(
            flagset![3, 4],
            decode_flagset("3", FlagType::default(), aliases).unwrap()
        );
        assert_eq!(
            flagset!['a' as u16],
            decode_flagset("a", FlagType::default(), aliases).unwrap()
        );

        assert_eq!(
            flagset![1],
            decode_flagset("1", FlagType::Numeric, aliases).unwrap()
        );
        assert_eq!(
            flagset!['1' as u16],
            decode_flagset("1", FlagType::default(), &[]).unwrap()
        );
    }

    #[test]
    fn parse_condition_test() {
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
    fn parse_compound_rule_test() {
        use super::ParseCompoundRuleError as Error;
        use crate::aff::CompoundRuleElement as Elem;

        assert_eq!(
            Ok(vec![
                Elem::Flag(flag!('a')),
                Elem::Flag(flag!('b')),
                Elem::ZeroOrOne,
                Elem::Flag(flag!('c')),
                Elem::ZeroOrMore,
                Elem::Flag(flag!('d')),
            ]),
            parse_compound_rule("ab?c*d", FlagType::Short)
        );

        // Hello, en_GB.aff
        assert_eq!(
            Ok(vec![
                Elem::Flag(flag!('#')),
                Elem::ZeroOrMore,
                Elem::Flag(flag!('0')),
                Elem::Flag(flag!('{')),
            ]),
            parse_compound_rule("#*0{", FlagType::Utf8)
        );

        assert_eq!(
            Ok(vec![
                Elem::Flag(flag!(5)),
                Elem::Flag(flag!(6)),
                Elem::ZeroOrMore,
                Elem::Flag(flag!(11)),
                Elem::ZeroOrOne,
                Elem::Flag(flag!(99)),
            ]),
            parse_compound_rule("(5)(6)*(11)?(99)", FlagType::Numeric)
        );

        assert_eq!(
            Ok(vec![
                Elem::Flag(flag!(10060)),
                Elem::Flag(flag!(10052)),
                Elem::ZeroOrMore,
                Elem::Flag(flag!(10056)),
                Elem::ZeroOrOne,
                Elem::Flag(flag!(17218)),
            ]),
            parse_compound_rule("(L')(D')*(H')?(BC)", FlagType::Long)
        );

        // Can't start with a wildcard
        assert_eq!(
            Err(Error::InvalidFormat),
            parse_compound_rule("*", FlagType::Short)
        );
        assert_eq!(
            Err(Error::InvalidFormat),
            parse_compound_rule("?", FlagType::Short)
        );
    }

    #[test]
    fn basic_prefix_test() {
        let dic = "0";
        // From `en_GB.aff`.
        let aff = r#"
        PFX A Y 2
        PFX A 0 re [^e]
        PFX A 0 re- e
        "#;

        let aff_data = parse(dic, aff, ahash::RandomState::new()).unwrap();
        assert_eq!(2, aff_data.prefixes.table.len());
        assert_eq!(
            Prefix::new(flag!('A'), true, None, "re", Some("[^e]"), flagset![]).unwrap(),
            aff_data.prefixes.table[0]
        );
        assert_eq!(
            Prefix::new(flag!('A'), true, None, "re-", Some("e"), flagset![]).unwrap(),
            aff_data.prefixes.table[1]
        );
    }
}
