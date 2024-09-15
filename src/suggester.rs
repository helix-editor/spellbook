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
        self.forgotten_char_suggest(word, out);
        // move_char_suggest
        self.wrong_char_suggest(word, out);
        // doubled_two_chars_suggest
        // two_words_suggest

        false
    }

    /// Adds a suggestion to the suggestion vector if it belongs to the dictionary and is not
    /// forbidden.
    ///
    /// About accepting `Into<Cow<str>>`: some callers have `String`s that need to be borrowed for
    /// lookup but can be pushed to the output vector without cloning. Some callers are `&str`s
    /// that need to be allocated to `String`s before being pushed. (We should do that conversion
    /// lazily though as the word might be incorrect.) The `Cow` covers both. (Also note the
    /// explicit lifetime but that's only because anonymous lifetimes are not allowed in this slot
    /// as of the current Rust version.)
    fn add_suggestion_if_correct<'w, W: Into<Cow<'w, str>>>(
        &self,
        word: W,
        out: &mut Vec<String>,
    ) -> bool {
        let word = word.into();
        let Some(flags) = self.checker.check_word(
            word.as_ref(),
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

        out.push(word.into_owned());
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
        if self.add_suggestion_if_correct(word, out) {
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
            buffer.remove(idx);
            self.add_suggestion_if_correct(buffer, out);
        }
    }

    /// Suggests edits to the word to add a missing character.
    fn forgotten_char_suggest(&self, word: &str, out: &mut Vec<String>) {
        let mut remaining_attempts = self.max_attempts_for_long_alogs(word);
        let mut buffer = String::from(word);
        for ch in self.checker.aff.try_chars.chars() {
            for (idx, _) in word.char_indices() {
                if remaining_attempts == 0 {
                    return;
                }
                remaining_attempts -= 1;
                buffer.insert(idx, ch);
                self.add_suggestion_if_correct(&buffer, out);
                buffer.remove(idx);
            }
        }
    }

    /// Suggests words with one "wrong" character swapped for another character from the TRY
    /// alphabet.
    ///
    /// For example this suggests "world" for "warld".
    fn wrong_char_suggest(&self, word: &str, out: &mut Vec<String>) {
        let mut remaining_attempts = self.max_attempts_for_long_alogs(word);
        let mut buffer = String::from(word);
        for ch in self.checker.aff.try_chars.chars() {
            for (idx, word_ch) in word.char_indices() {
                if ch == word_ch {
                    continue;
                }
                if remaining_attempts == 0 {
                    return;
                }
                remaining_attempts -= 1;
                buffer.remove(idx);
                buffer.insert(idx, ch);
                self.add_suggestion_if_correct(&buffer, out);
                buffer.remove(idx);
                buffer.insert(idx, word_ch);
            }
        }
    }

    /// Determines a reasonable number of attempts to try at editing a word.
    ///
    /// This limits the impact of guessing edits for complicated dictionaries: whether a
    /// dictionary allows compounding and how many prefixes/suffixes a dictionary uses.
    /// (And whether it allows complex prefixes.)
    fn max_attempts_for_long_alogs(&self, word: &str) -> usize {
        let p = self.checker.aff.prefixes.len() as u64 / 20u64;
        let s = self.checker.aff.suffixes.len() as u64 / 20u64;
        let mut cost = 1 + p + s + p * s;
        if self.checker.aff.options.complex_prefixes {
            cost += p * p + 2 * s * p * p;
        } else {
            cost += s * s + 2 * p * s * s;
        }
        cost = cost.clamp(250_000, 25_000_000_000);
        let mut attempts = 25_000_000_000 / cost;
        if self.checker.aff.options.allows_compounding() {
            attempts /= word.len() as u64;
        }
        attempts
            .try_into()
            .expect("clamping and divisions should ensure this can fit into usize")
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

    #[test]
    fn forgotten_char_suggest() {
        assert!(suggest("helo").contains(&"hello".to_string()));
        assert!(suggest("wrld").contains(&"world".to_string()));
    }

    #[test]
    fn wrong_char_suggest() {
        let suggestions = suggest("faver");
        assert!(suggestions.contains(&"fiver".to_string()));
        //                              ^
        assert!(suggestions.contains(&"faker".to_string()));
        //                               ^
        assert!(suggestions.contains(&"favor".to_string()));
        //                                ^
    }
}
