use core::hash::BuildHasher;

use crate::{
    alloc::{borrow::Cow, string::String, vec::Vec},
    checker::{Checker, Forceucase, HiddenHomonym},
    classify_casing, Casing, AT_COMPOUND_BEGIN, MAX_WORD_LEN,
};

macro_rules! has_flag {
    ( $flags:expr, $flag:expr ) => {{
        match $flag {
            Some(flag) => $flags.contains(&flag),
            None => false,
        }
    }};
}

pub(crate) struct Suggester<'a, S: BuildHasher> {
    checker: Checker<'a, S>,
}

impl<'a, S: BuildHasher> Suggester<'a, S> {
    pub fn new(checker: Checker<'a, S>) -> Self {
        Self { checker }
    }

    pub fn suggest(&self, word: &str, out: &mut Vec<String>) {
        out.clear();
        if word.len() >= MAX_WORD_LEN {
            return;
        }

        self.suggest_impl(word, out);
    }

    fn suggest_impl(&self, word: &str, out: &mut Vec<String>) {
        if word.is_empty() {
            return;
        }

        // ICONV
        let word = self.checker.aff.input_conversions.convert(word);
        let casing = classify_casing(&word);
        let mut hq_suggestions = false;

        match casing {
            Casing::None => {
                // ?
                if self
                    .checker
                    .aff
                    .options
                    .compound_force_uppercase_flag
                    .is_some()
                    && self
                        .checker
                        .check_compound::<AT_COMPOUND_BEGIN>(&word, Forceucase::AllowBadForceucase)
                        .is_some()
                {
                    out.push(self.checker.aff.options.case_handling.titlecase(&word));
                    return;
                }
                hq_suggestions |= self.suggest_low(&word, out);
            }
            _ => todo!(),
        }

        // TODO: remove. Currently used to suppress an unused_variable lint.
        assert!(!hq_suggestions);

        // OCONV
        for suggestion in out.iter_mut() {
            match self.checker.aff.output_conversions.convert(suggestion) {
                Cow::Borrowed(_) => (),
                Cow::Owned(converted) => *suggestion = converted,
            }
        }
    }

    fn suggest_low(&self, word: &str, out: &mut Vec<String>) -> bool {
        // let len = out.len();
        self.uppercase_suggest(word, out);
        // rep_suggest
        // map_suggest
        // Then check if the word is correct, set `hq_suggestions` based on that.
        // adjacent_swap_suggest
        // distant_swap_suggest
        // keyboard_suggest
        self.extra_char_suggest(word, out);
        // extra_char_suggest
        // forgotten_char_suggest
        // move_char_suggest
        // bad_char_suggest
        // doubled_two_chars_suggest
        // two_words_suggest

        false
    }

    // TODO: what to take here... a &str? a String? a Cow<str>?
    fn add_suggestion_if_correct(&self, word: String, out: &mut Vec<String>) -> bool {
        let Some(flags) = self.checker.check_word(
            &word,
            Forceucase::ForbidBadForceucase,
            HiddenHomonym::SkipHiddenHomonym,
        ) else {
            return false;
        };

        if has_flag!(flags, self.checker.aff.options.forbidden_word_flag) {
            return false;
        }

        if self.checker.aff.options.forbid_warn
            && has_flag!(flags, self.checker.aff.options.warn_flag)
        {
            return false;
        }

        out.push(word);
        true
    }

    fn uppercase_suggest(&self, word: &str, out: &mut Vec<String>) {
        let upper = self.checker.aff.options.case_handling.uppercase(word);
        self.add_suggestion_if_correct(upper, out);
    }

    fn extra_char_suggest(&self, word: &str, out: &mut Vec<String>) {
        // TODO: many suggestion strategies use a String buffer.
        // Allocate it up front and reuse it for each of these checks?
        for (idx, _ch) in word.char_indices() {
            let mut buffer = String::from(word);
            // TODO: drop assert_eq
            buffer.remove(idx);
            self.add_suggestion_if_correct(buffer, out);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        alloc::{string::ToString, vec},
        EN_US,
    };

    fn suggest(word: &str) -> Vec<String> {
        let mut suggestions = Vec::new();
        EN_US.suggest(word, &mut suggestions);
        suggestions
    }

    #[test]
    fn empty_suggest() {
        assert!(suggest("").is_empty());
    }

    #[test]
    fn huge_word_is_skipped() {
        assert!(suggest(&"hello".repeat(MAX_WORD_LEN)).is_empty());
    }

    #[test]
    fn existing_suggestions_are_cleared() {
        let mut suggestions = Vec::new();
        suggestions.push("example".to_string());
        EN_US.suggest("", &mut suggestions);
        assert!(suggestions.is_empty())
    }

    #[test]
    fn uppercase_suggest() {
        // "ANSI" is correct in en_US and not "ansi".
        assert!(suggest("ansi").contains(&"ANSI".to_string()));
    }

    #[test]
    fn extra_char_suggest() {
        assert!(suggest("adveenture").contains(&"adventure".to_string()));
    }
}
