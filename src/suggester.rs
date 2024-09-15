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

        // Some suggestion methods can cause duplicates. For example in "adveenture",
        // extra_char_suggest can eliminate either inner 'e' causing a duplicate "adventure"
        // suggestion. Deduplicate the results while preserving order:
        deduplicate(out);

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
        self.rep_suggest(word, out);
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

    /// Suggests the word, uppercased, if valid.
    ///
    /// For example you might type "ansi" and mean "ANSI".
    fn uppercase_suggest(&self, word: &str, out: &mut Vec<String>) {
        let upper = self.checker.aff.options.case_handling.uppercase(word);
        self.add_suggestion_if_correct(upper, out);
    }

    /// Suggests edits to the word based on the replacement table (`REP`) defined in the `.aff`
    /// file.
    ///
    /// REP is used by a dictionary to list common misspellings or similar sounding word parts.
    /// For example in en_US "shun" has the same sound as "tion" which is typically the correct
    /// word part.
    fn rep_suggest(&self, word: &str, out: &mut Vec<String>) {
        // See `Checker::is_rep_similar` for notes about the way this function is written and
        // allocations
        for (from, to) in self.checker.aff.replacements.whole_word_replacements() {
            if word == from {
                self.try_rep_suggestion(to, out);
            }
        }

        if self
            .checker
            .aff
            .replacements
            .has_only_whole_word_replacements()
        {
            return;
        }

        let mut scratch = String::from(word);

        for (from, to) in self.checker.aff.replacements.start_word_replacements() {
            if word.starts_with(from) {
                scratch.replace_range(..from.len(), to);
                self.try_rep_suggestion(&scratch, out);
                scratch.replace_range(..to.len(), from);
            }
        }

        debug_assert_eq!(&scratch, word);

        for (from, to) in self.checker.aff.replacements.end_word_replacements() {
            let Some(idx) = word.len().checked_sub(from.len()) else {
                continue;
            };
            if &word[idx..] == from {
                scratch.replace_range(idx.., to);
                self.try_rep_suggestion(&scratch, out);
                scratch.replace_range(idx.., from);
            }
        }

        debug_assert_eq!(&scratch, word);

        for (from, to) in self.checker.aff.replacements.any_place_replacements() {
            for (idx, _) in word.match_indices(from) {
                scratch.replace_range(idx..idx + from.len(), to);
                self.try_rep_suggestion(&scratch, out);
                scratch.replace_range(idx..idx + to.len(), from);
            }
        }

        debug_assert_eq!(&scratch, word);
    }

    fn try_rep_suggestion(&self, word: &str, out: &mut Vec<String>) {
        // TODO: figure out what to pass this function.
        if self.add_suggestion_if_correct(String::from(word), out) {
            return;
        }

        // ?
        let Some(mut j) = word.find(' ') else {
            return;
        };
        let mut i = 0;
        loop {
            let part = &word[i..j - i];
            if self
                .checker
                .check_word(
                    part,
                    Forceucase::ForbidBadForceucase,
                    HiddenHomonym::SkipHiddenHomonym,
                )
                .is_none()
            {
                return;
            }
            i = j + 1;
            let Some(idx) = word[i..].find(' ') else {
                break;
            };
            j = idx + i;
        }

        out.push(String::from(word));
    }

    /// Suggests edits to the word to drop any character.
    ///
    /// Intuitively you might double-tap a character key on your keyboard.
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

/// Removes all duplicate items in a vector while preserving order.
///
/// This works similarly to C++'s iterator `remove(begin, end, value)`: we swap duplicate elements
/// to the end of the vector and then truncate the vector to eliminate the duplicates.
fn deduplicate<T: Eq>(items: &mut Vec<T>) {
    if items.is_empty() {
        return;
    }

    let mut idx = 0;
    let mut last = items.len();
    while idx < last {
        let Some(first) = items[idx + 1..last].iter().position(|i| i == &items[idx]) else {
            idx += 1;
            continue;
        };
        let mut first = first + idx + 1;
        let mut result = first;
        first += 1;
        while first < last {
            if items[first] != items[idx] {
                items.swap(result, first);
                result += 1;
            }
            first += 1;
        }
        idx += 1;
        last = result;
    }

    items.truncate(last);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        alloc::{string::ToString, vec},
        EN_US,
    };

    #[test]
    fn deduplicate_test() {
        fn deduplicate<T: Eq, I: Into<Vec<T>>>(items: I) -> Vec<T> {
            let mut items = items.into();
            super::deduplicate(&mut items);
            items
        }

        assert_eq!(deduplicate([1, 1, 2, 2, 3, 3]), vec![1, 2, 3]);
        assert_eq!(deduplicate([1, 2, 3, 3]), vec![1, 2, 3]);
        assert_eq!(deduplicate([1, 2, 3, 2, 3, 1]), vec![1, 2, 3]);
        assert_eq!(deduplicate([1, 1]), vec![1]);
        assert_eq!(deduplicate([1]), vec![1]);
        assert_eq!(deduplicate::<usize, _>([]), vec![]);
    }

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

    #[test]
    fn rep_suggest() {
        // Uses the en_US `REP size cise`. Sounds similar but "cise" is correct here.
        assert!(suggest("exsize").contains(&"excise".to_string()));
    }
}
