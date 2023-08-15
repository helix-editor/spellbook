//! Functions for parsing `.aff` files into the Aff type.

use std::{
    iter::{Enumerate, Peekable},
    rc::Rc,
    str::Lines,
};

use regex::Regex;

use super::{Aff, Casing, FlagType};
use crate::{
    dic::parser::split_word_and_flags, Flag, MorphologicalFields, ParseDictionaryError,
    ParseDictionaryErrorKind,
};

// This parser takes some inspiration from zspell's work.
// See <https://github.com/pluots/zspell/blob/71ae77932f2cc67f593d846a26a9ffd7cf6d0412/crates/zspell/src/parser_affix.rs>.

type Result<T> = core::result::Result<T, ParseDictionaryError>;
type ParseResult = Result<bool>;

const AFF_PARSERS: [fn(&mut Context) -> ParseResult; 41] = [
    parse_encoding,
    parse_flag_type,
    parse_ignore,
    parse_language,
    parse_key,
    parse_try_chars,
    parse_forbidden_flag,
    parse_circumfix_flag,
    parse_keep_case_flag,
    parse_need_affix_flag,
    parse_no_suggest_flag,
    parse_compound_flag,
    parse_compound_begin_flag,
    parse_compound_last_flag,
    parse_compound_middle_flag,
    parse_only_in_compound_flag,
    parse_compound_permit_flag,
    parse_compound_forbid_flag,
    parse_force_ucase_flag,
    parse_check_sharps,
    parse_no_split_suggestions,
    parse_only_max_diff,
    parse_complex_prefixes,
    parse_full_strip,
    parse_check_compound_case,
    parse_check_compound_dupe,
    parse_check_compound_replacement,
    parse_check_compound_triple,
    parse_simplified_triple,
    parse_compound_more_suffixes,
    parse_max_compound_suggestions,
    parse_ngram_suggestions,
    parse_max_diff,
    parse_compound_min_length,
    parse_max_compound_word_count,
    parse_compound_rules,
    parse_flag_set_aliases,
    parse_break_patterns,
    // parse_map_chars,
    parse_replacements,
    parse_prefixes,
    parse_suffixes,
];

pub(crate) fn parse(text: &str) -> Result<Aff> {
    let mut cx = Context::new(text);

    while !cx.is_finished() {
        for parser in AFF_PARSERS.iter() {
            if parser(&mut cx)? {
                break;
            }
        }
        cx.advance_line();
    }

    if cx.aff.break_patterns.is_empty() {
        // Default break patterns when not specified
        cx.aff.break_patterns.push(Regex::new("^-").unwrap());
        cx.aff.break_patterns.push(Regex::new("-").unwrap());
        cx.aff.break_patterns.push(Regex::new("-$").unwrap());
    }

    Ok(cx.aff)
}
fn parse_encoding(cx: &mut Context) -> ParseResult {
    cx.parse_str("SET", |cx, str| {
        cx.aff.encoding = str.into();
    })
}

fn parse_flag_type(cx: &mut Context) -> ParseResult {
    cx.parse_key_for_one_word("FLAG", |cx, s| {
        s.parse::<FlagType>()
            .map(|flag_type| {
                cx.aff.flag_type = flag_type;
                true
            })
            .map_err(|err| cx.error(ParseDictionaryErrorKind::UnknownFlagType(err)))
    })
}

fn parse_ignore(cx: &mut Context) -> ParseResult {
    cx.parse_str("IGNORE", |cx, str| {
        cx.aff.ignore_chars = Some(str.into());
    })
}

fn parse_language(cx: &mut Context) -> ParseResult {
    cx.parse_str("LANG", |cx, str| {
        cx.aff.language_id = Some(str.to_string());
        if ["tr", "tr_TR", "az", "crh"].contains(&str) {
            cx.aff.casing = Casing::Turkic;
        }
    })
}

fn parse_key(cx: &mut Context) -> ParseResult {
    cx.parse_str("KEY", |cx, str| {
        cx.aff.key = str.to_string();
    })
}

fn parse_try_chars(cx: &mut Context) -> ParseResult {
    cx.parse_str("TRY", |cx, str| {
        cx.aff.try_chars = str.to_string();
    })
}

fn parse_forbidden_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("FORBIDDENWORD", |cx, flag| {
        cx.aff.forbidden_word_flag = Some(flag);
    })
}

fn parse_circumfix_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("CIRCUMFIX", |cx, flag| {
        cx.aff.circumfix_flag = Some(flag);
    })
}

fn parse_keep_case_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("KEEPCASE", |cx, flag| {
        cx.aff.keep_case_flag = Some(flag);
    })
}

fn parse_need_affix_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("NEEDAFFIX", |cx, flag| {
        cx.aff.need_affix_flag = Some(flag);
    })
}

fn parse_no_suggest_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("NOSUGGEST", |cx, flag| {
        cx.aff.no_suggest_flag = Some(flag);
    })
}

fn parse_compound_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDFLAG", |cx, flag| {
        cx.aff.compound_flag = Some(flag);
    })
}

fn parse_compound_begin_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDBEGIN", |cx, flag| {
        cx.aff.compound_begin_flag = Some(flag);
    })
}

fn parse_compound_middle_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDMIDDLE", |cx, flag| {
        cx.aff.compound_middle_flag = Some(flag);
    })
}

fn parse_compound_last_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDLAST", |cx, flag| {
        cx.aff.compound_end_flag = Some(flag);
    })
}

fn parse_only_in_compound_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("ONLYINCOMPOUND", |cx, flag| {
        cx.aff.only_in_compound_flag = Some(flag);
    })
}

fn parse_compound_permit_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDPERMITFLAG", |cx, flag| {
        cx.aff.compound_permit_flag = Some(flag);
    })
}

fn parse_compound_forbid_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("COMPOUNDFORBIDFLAG", |cx, flag| {
        cx.aff.compound_forbid_flag = Some(flag);
    })
}

fn parse_force_ucase_flag(cx: &mut Context) -> ParseResult {
    cx.parse_flag("FORCEUCASE", |cx, flag| {
        cx.aff.force_uppercase_flag = Some(flag);
    })
}

fn parse_check_sharps(cx: &mut Context) -> ParseResult {
    cx.parse_bool("CHECKSHARPS", |cx| {
        cx.aff.check_sharps = true;
        cx.aff.casing = Casing::Germanic;
    })
}

fn parse_no_split_suggestions(cx: &mut Context) -> ParseResult {
    cx.parse_bool("NOSPLITSUGS", |cx| cx.aff.no_split_suggestions = true)
}

fn parse_only_max_diff(cx: &mut Context) -> ParseResult {
    cx.parse_bool("ONLYMAXDIFF", |cx| cx.aff.only_max_diff = true)
}

fn parse_complex_prefixes(cx: &mut Context) -> ParseResult {
    cx.parse_bool("COMPLEXPREFIXES", |cx| cx.aff.complex_prefixes = true)
}

fn parse_full_strip(cx: &mut Context) -> ParseResult {
    cx.parse_bool("FULLSTRIP", |cx| cx.aff.full_strip = true)
}

fn parse_check_compound_case(cx: &mut Context) -> ParseResult {
    cx.parse_bool("CHECKCOMPOUNDCASE", |cx| cx.aff.check_compound_case = true)
}

fn parse_check_compound_dupe(cx: &mut Context) -> ParseResult {
    cx.parse_bool("CHECKCOMPOUNDDUP", |cx| cx.aff.check_compound_dupe = true)
}

fn parse_check_compound_replacement(cx: &mut Context) -> ParseResult {
    cx.parse_bool("CHECKCOMPOUNDREP", |cx| {
        cx.aff.check_compound_replacement = true
    })
}

fn parse_check_compound_triple(cx: &mut Context) -> ParseResult {
    cx.parse_bool("CHECKCOMPOUNDTRIPLE", |cx| {
        cx.aff.check_compound_triple = true
    })
}

fn parse_simplified_triple(cx: &mut Context) -> ParseResult {
    cx.parse_bool("SIMPLIFIEDTRIPLE", |cx| cx.aff.simplified_triple = true)
}

fn parse_compound_more_suffixes(cx: &mut Context) -> ParseResult {
    cx.parse_bool("COMPOUNDMORESUFFIXES", |cx| {
        cx.aff.compound_more_suffixes = true
    })
}

fn parse_max_compound_suggestions(cx: &mut Context) -> ParseResult {
    cx.parse_int("MAXCPDSUGS", |cx, n| {
        cx.aff.max_compound_suggestions = n;
    })
}

fn parse_ngram_suggestions(cx: &mut Context) -> ParseResult {
    cx.parse_int("MAXNGRAMSUGS", |cx, n| {
        cx.aff.max_ngram_suggestions = n;
    })
}

fn parse_max_diff(cx: &mut Context) -> ParseResult {
    cx.parse_int("MAXDIFF", |cx, n| {
        cx.aff.max_diff = n;
    })
}

fn parse_compound_min_length(cx: &mut Context) -> ParseResult {
    cx.parse_int("COMPOUNDMIN", |cx, n| {
        cx.aff.compound_min_length = n;
    })
}

fn parse_max_compound_word_count(cx: &mut Context) -> ParseResult {
    cx.parse_int("COMPOUNDWORDMAX", |cx, n| {
        cx.aff.max_compound_word_count = Some(n);
    })
}

fn parse_compound_rules(cx: &mut Context) -> ParseResult {
    cx.parse_table1("COMPOUNDRULE", |cx, s| {
        let rule = super::CompoundRule::new(s, cx.aff.flag_type)
            .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedCompoundRule(err)))?;
        cx.aff.compound_rules.push(rule);
        Ok(())
    })
}

fn parse_flag_set_aliases(cx: &mut Context) -> ParseResult {
    cx.parse_table1("AF", |cx, s| {
        let flag_set = cx
            .aff
            .flag_type
            .parse_flags_from_chars(s.chars())
            .map_err(|err| cx.error(err.into()))?;
        cx.aff.flag_set_aliases.push(flag_set);
        Ok(())
    })
}

fn parse_break_patterns(cx: &mut Context) -> ParseResult {
    fn parse_break_pattern(pattern: &str) -> core::result::Result<Regex, regex::Error> {
        let pattern = regex::escape(pattern)
            .replace("\\^", "^")
            .replace("\\$", "$");
        // TODO: can we drop the `format!` calls here? I don't see any point to
        // the parens other than using the captures API, and regex seems to drop
        // the capture group for the first branch here.
        if pattern.starts_with('^') || pattern.ends_with('$') {
            Regex::new(&format!("({pattern})"))
        } else {
            Regex::new(&format!(".({pattern})."))
        }
    }

    cx.parse_table1("BREAK", |cx, s| {
        let break_pattern = parse_break_pattern(s)
            .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedRegex(err)))?;
        cx.aff.break_patterns.push(break_pattern);
        Ok(())
    })
}

// TODO: Multiple characters might be replaced. The syntax uses paretheses to group
// those strings.
// fn parse_map_chars(cx: &mut Context) -> ParseResult {
//     cx.parse_table1("MAP", |cx, s| {
//     })
// }

fn parse_replacements(cx: &mut Context) -> ParseResult {
    cx.parse_table2("REP", |cx, word1, word2| {
        let replacement = super::ReplacementPattern::new(word1, word2)
            .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedRegex(err)))?;
        cx.aff.replacements.push(replacement);
        Ok(())
    })
}

fn parse_prefixes(cx: &mut Context) -> ParseResult {
    cx.parse_affix_table(
        "PFX",
        |cx, flag, crossproduct, strip, add, condition, morphological_fields| {
            let (add, flag_set) = split_word_and_flags(&cx.aff, add)
                .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedFlag(err)))?;

            let prefix = super::Prefix::new(
                flag,
                crossproduct,
                strip,
                add,
                condition,
                flag_set,
                morphological_fields,
            )
            .map(Rc::new)
            .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedRegex(err)))?;

            cx.aff
                .prefixes
                .entry(prefix.flag)
                .or_insert_with(Default::default)
                .push(prefix.clone());
            // Appease the borrow checker by creating a temporary clone of the Rc
            // that lives long enough to insert the intended Rc<Prefix> into the trie.
            let char_prefix = prefix.clone();
            let chars = char_prefix.add.chars();
            cx.aff.prefixes_index.push(chars, prefix);

            Ok(())
        },
    )
}

fn parse_suffixes(cx: &mut Context) -> ParseResult {
    cx.parse_affix_table(
        "SFX",
        |cx, flag, crossproduct, strip, add, condition, morphological_fields| {
            let (add, flag_set) = split_word_and_flags(&cx.aff, add)
                .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedFlag(err)))?;

            let suffix = super::Suffix::new(
                flag,
                crossproduct,
                strip,
                add,
                condition,
                flag_set,
                morphological_fields,
            )
            .map(Rc::new)
            .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedRegex(err)))?;

            cx.aff
                .suffixes
                .entry(suffix.flag)
                .or_insert_with(Default::default)
                .push(suffix.clone());
            // Appease the borrow checker by creating a temporary clone of the Rc
            // that lives long enough to insert the intended Rc<Suffix> into the trie.
            let char_suffix = suffix.clone();
            let chars = char_suffix.add.chars().rev();
            cx.aff.suffixes_index.push(chars, suffix);

            Ok(())
        },
    )
}

#[derive(Debug)]
struct Context<'a> {
    aff: Aff,
    lines: Peekable<Enumerate<Lines<'a>>>,
}

/// A helper type that means "words on a line split by whitespace with comments
/// dropped." This is a concretion of `impl Iterator<Item = &'a str>`.
type Words<'a> =
    std::iter::TakeWhile<std::str::SplitWhitespace<'a>, for<'b, 'c> fn(&'b &'c str) -> bool>;

impl<'a> Context<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            lines: text.lines().enumerate().peekable(),
            aff: Aff::default(),
        }
    }

    fn is_finished(&mut self) -> bool {
        self.lines.peek().is_none()
    }

    fn parse_key_line<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self, Words<'a>) -> ParseResult,
    {
        match self.split_key_line(key) {
            Some(words) => f(self, words),
            None => Ok(false),
        }
    }

    /// A parser that matches when the given key matches and the rest
    /// of the line only contains one word. That word is passed to the
    /// given map function for further parsing.
    fn parse_key_for_one_word<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self, &'a str) -> ParseResult,
    {
        self.parse_key_line(key, |cx, words| {
            let word = cx.take_exactly_one_word(words)?;
            f(cx, word)
        })
    }

    fn parse_flag<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self, Flag),
    {
        self.parse_key_for_one_word(key, |cx, s| {
            let flag = cx
                .aff
                .flag_type
                .parse_flag_from_str(s)
                .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedFlag(err)))?;
            f(cx, flag);
            Ok(true)
        })
    }

    fn parse_str<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self, &str),
    {
        self.parse_key_for_one_word(key, |cx, s| {
            f(cx, s);
            Ok(true)
        })
    }

    fn parse_bool<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self),
    {
        self.parse_key_line(key, |cx, words| {
            let count = words.count();
            if count == 0 {
                f(cx);
                Ok(true)
            } else {
                Err(cx.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 0,
                    actual: count,
                }))
            }
        })
    }

    fn parse_int<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: FnOnce(&mut Self, usize),
    {
        self.parse_key_for_one_word(key, |cx, s| {
            let number = s
                .parse::<usize>()
                .map_err(|err| cx.error(ParseDictionaryErrorKind::MalformedNumber(err)))?;
            f(cx, number);
            Ok(true)
        })
    }

    // Regular 1-word tables like MAP or BREAK, not affix tables (PFX, SFX).
    fn parse_table1<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: Fn(&mut Self, &'a str) -> Result<()>,
    {
        let rows = match self.split_key_line(key) {
            Some(words) => self
                .take_exactly_one_word(words)?
                .parse::<usize>()
                .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?,
            None => return Ok(false),
        };

        for row in 1..=rows {
            self.advance_line();
            let word = match self.split_key_line(key) {
                Some(words) => self.take_exactly_one_word(words)?,
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                        expected: rows,
                        actual: row - 1,
                    }))
                }
            };
            f(self, word)?;
        }

        Ok(true)
    }

    // 2-word tables like ICONV/OCONV/REP.
    fn parse_table2<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        F: Fn(&mut Self, &'a str, &'a str) -> Result<()>,
    {
        let rows = match self.split_key_line(key) {
            Some(words) => self
                .take_exactly_one_word(words)?
                .parse::<usize>()
                .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?,
            None => return Ok(false),
        };

        for row in 1..=rows {
            self.advance_line();
            match self.split_key_line(key) {
                Some(mut words) => {
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
                    f(self, word1, word2)?;
                }
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                        expected: rows,
                        actual: row - 1,
                    }))
                }
            }
        }

        Ok(true)
    }

    fn parse_affix_table<F>(&mut self, key: &str, f: F) -> ParseResult
    where
        // cx, flag, is_crossproduct, stripping, add, [condition, [morphological_fields]]
        F: Fn(
            &mut Self,
            Flag,
            bool,
            &'a str,
            &'a str,
            Option<&'a str>,
            MorphologicalFields,
        ) -> Result<()>,
    {
        let mut words = match self.split_key_line(key) {
            Some(words) => words,
            None => return Ok(false),
        };

        let flag = match words.next() {
            Some(word) => self
                .aff
                .flag_type
                .parse_flag_from_str(word)
                .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedFlag(err)))?,
            None => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
        };

        let is_crossproduct = match words.next() {
            Some("Y") => true,
            Some("N") => false,
            _ => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
        };

        let rows = match words.next() {
            Some(word) => word
                .parse::<usize>()
                .map_err(|err| self.error(ParseDictionaryErrorKind::MalformedNumber(err)))?,
            None => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
        };

        for row in 1..=rows {
            self.advance_line();
            match self.split_key_line(key) {
                Some(mut words) => {
                    let inner_flag = match words.next() {
                        Some(word) => {
                            self.aff
                                .flag_type
                                .parse_flag_from_str(word)
                                .map_err(|err| {
                                    self.error(ParseDictionaryErrorKind::MalformedFlag(err))
                                })?
                        }
                        None => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
                    };
                    if inner_flag != flag {
                        return Err(self.error(ParseDictionaryErrorKind::MalformedAffix));
                    }

                    let stripping = match words.next() {
                        Some("0") => "",
                        Some(word) => word,
                        None => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
                    };

                    let add = match words.next() {
                        Some("0") => "",
                        Some(word) => word,
                        None => return Err(self.error(ParseDictionaryErrorKind::MalformedAffix)),
                    };

                    let condition = match words.next() {
                        Some(".") | None => None,
                        Some(word) => Some(word),
                    };

                    let mut morphological_fields: MorphologicalFields = Default::default();
                    // Current behavior is to drop any that can't be parsed.
                    for part in words {
                        match part.split_once(':') {
                            Some((key, value)) => {
                                let mut keychars = key.chars();
                                let k1 = match keychars.next() {
                                    Some(ch) => ch,
                                    None => continue,
                                };
                                let k2 = match keychars.next() {
                                    Some(ch) => ch,
                                    None => continue,
                                };
                                if value.is_empty() {
                                    continue;
                                }

                                morphological_fields
                                    .entry([k1, k2])
                                    .or_insert_with(Default::default)
                                    .push(value.to_string());
                            }
                            None => continue,
                        };
                    }

                    f(
                        self,
                        flag,
                        is_crossproduct,
                        stripping,
                        add,
                        condition,
                        morphological_fields,
                    )?;
                }
                None => {
                    return Err(self.error(ParseDictionaryErrorKind::MismatchedRowCount {
                        expected: rows,
                        actual: row - 1,
                    }))
                }
            };
        }

        Ok(true)
    }

    /// Splits the key from the current line and returns remaining words on the line
    /// separated by whitespace with comments dropped.
    /// Returns `None` if the key is not found at the start of the current line.
    fn split_key_line(&mut self, key: &str) -> Option<Words<'a>> {
        let (_line_number, line) = self.lines.peek()?;

        if !line.starts_with(key) {
            return None;
        }

        let words = line[key.len()..]
            .split_whitespace()
            .take_while((|word| !word.starts_with('#')) as for<'b, 'c> fn(&'b &'c str) -> bool);

        Some(words)
    }

    /// Split the first word from the words, returning an arity mismatch
    /// error if there is not exactly one word in the iterator.
    fn take_exactly_one_word(&mut self, mut words: Words<'a>) -> Result<&'a str> {
        let word = match words.next() {
            Some(word) => word,
            None => {
                return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                    expected: 1,
                    actual: 0,
                }))
            }
        };

        let rest = words.count();
        if rest != 0 {
            return Err(self.error(ParseDictionaryErrorKind::MismatchedArity {
                expected: 1,
                actual: 1 + rest,
            }));
        }

        Ok(word)
    }

    fn advance_line(&mut self) {
        self.lines.next();
    }

    fn error(&mut self, kind: ParseDictionaryErrorKind) -> ParseDictionaryError {
        ParseDictionaryError {
            kind,
            source: crate::ParseDictionaryErrorSource::Aff,
            line_number: self
                .lines
                .peek()
                .map(|(line_number, _line)| line_number)
                .copied(),
        }
    }
}
