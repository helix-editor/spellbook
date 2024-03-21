use core::hash::BuildHasher;

use crate::{aff::AffData, stdx::is_some_and, FlagSet};

// Nuspell limits the length of the input word:
// <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/src/nuspell/dictionary.cxx#L156>
const MAX_WORD_LEN: usize = 360;

const MAX_BREAK_DEPTH: usize = 9;

// TODO: expose type and add options to it?
pub(crate) struct Checker<'a, S: BuildHasher> {
    aff: &'a AffData<S>,
}

impl<'a, S: BuildHasher> Checker<'a, S> {
    pub fn new(aff: &'a AffData<S>) -> Self {
        Self { aff }
    }

    /// Checks that the word is valid according to the dictionary.
    pub fn check(&self, word: &str) -> bool {
        if word.len() > MAX_WORD_LEN {
            return false;
        }

        // TODO: iconv

        if word.is_empty() {
            return true;
        }

        // TODO: abbreviation
        let trimmed_word = word.trim_end_matches('.');
        let abbreviated = trimmed_word.len() != word.len();

        if is_number(trimmed_word) {
            return true;
        }

        // TODO: erase chars in `trimmed_word`

        if self.spell_break(trimmed_word, 0) {
            return true;
        }

        if abbreviated {
            // TODO: erase chars in `word` - or figure out abbreviation after ignore-chars.
            // TODO: only keep one `.`?
            return self.spell_break(word, 0);
        }

        false
    }

    /// Recursively breaks up a word according to the dictionary's `BREAK` rules and checks that
    /// each broken word is correct.
    fn spell_break(&self, word: &str, depth: usize) -> bool {
        if let Some(flags) = &self.spell_casing(word) {
            if is_some_and(self.aff.options.forbidden_word_flag, |flag| {
                flags.contains(&flag)
            }) {
                return false;
            }

            if self.aff.options.forbid_warn
                && is_some_and(self.aff.options.warn_flag, |flag| flags.contains(&flag))
            {
                return false;
            }

            return true;
        }

        if depth == MAX_BREAK_DEPTH {
            return false;
        }

        for pattern in self.aff.break_table.start_word_breaks() {
            if let Some(rest) = word.strip_prefix(pattern) {
                if self.spell_break(rest, depth + 1) {
                    return true;
                }
            }
        }

        for pattern in self.aff.break_table.end_word_breaks() {
            if let Some(rest) = word.strip_suffix(pattern) {
                if self.spell_break(rest, depth + 1) {
                    return true;
                }
            }
        }

        for pattern in self.aff.break_table.middle_word_breaks() {
            // Break the word into two - dropping the pattern - and check that both parts are
            // correct.
            if let Some((part1, part2)) = word.split_once(pattern) {
                // If the match is at the end of the string then it's not a middle word break.
                if part2.is_empty() {
                    continue;
                }

                if !self.spell_break(part1, depth + 1) {
                    continue;
                }

                if self.spell_break(part2, depth + 1) {
                    return true;
                }
            }
        }

        false
    }

    fn spell_casing(&self, _word: &str) -> Option<&'a FlagSet> {
        // Classify the casing
        // For lowercase, camel & pascal `check_word`
        // For uppercase, spell_casing_upper
        // For title, spell_casing_title

        None
    }
}

/// Checks if the input word is a number.
///
/// Numbers may have a leading `-` and can have separators within the number of `,`, `.` or `-`,
/// but not more than one separating digits.
fn is_number(word: &str) -> bool {
    let word = word.strip_prefix('-').unwrap_or(word);
    if word.is_empty() {
        return false;
    }

    let mut separated = true;
    for ch in word.chars() {
        match ch {
            '0'..='9' => separated = false,
            '.' | '-' | ',' if !separated => separated = true,
            _ => return false,
        }
    }

    true
}

/// The capitalization of a word.
// Hunspell: <https://github.com/hunspell/hunspell/blob/8f9bb2957bfd74ca153fad96083a54488b518ca5/src/hunspell/csutil.hxx#L91-L96>
// Nuspell: <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/src/nuspell/utils.hxx#L91-L104>
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn is_number_nuspell_unit_test() {
        // Upstream: <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/tests/unit_test.cxx#L461-L471>

        assert!(!is_number(""));
        assert!(is_number("1234567890"));
        assert!(is_number("-1234567890"));
        assert!(is_number("123.456.78-9,0"));
        assert!(is_number("-123.456.78-9,0"));
        assert!(!is_number("123..456.78-9,0"));
        assert!(!is_number("123.456.-78-9,0"));
        assert!(!is_number("123..456.78-9-,0"));
    }

    #[test]
    fn classify_casing_nuspell_unit_test() {
        // Upstream: <https://github.com/nuspell/nuspell/blob/349e0d6bc68b776af035ca3ff664a7fc55d69387/tests/unit_test.cxx#L451-L459>

        assert_eq!(Casing::None, classify_casing(""));
        assert_eq!(Casing::None, classify_casing("здраво"));
        assert_eq!(Casing::Init, classify_casing("Здраво"));
        assert_eq!(Casing::All, classify_casing("ЗДРАВО"));
        assert_eq!(Casing::Camel, classify_casing("здРаВо"));
        assert_eq!(Casing::Pascal, classify_casing("ЗдрАво"));
    }
}
