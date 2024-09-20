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
        self.adjacent_swap_suggest(word, out);
        self.distant_swap_suggest(word, out);
        self.keyboard_suggest(word, out);
        self.extra_char_suggest(word, out);
        self.forgotten_char_suggest(word, out);
        // move_char_suggest
        self.wrong_char_suggest(word, out);
        self.doubled_two_chars_suggest(word, out);
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

    /// Suggests swapping two adjacent characters.
    ///
    /// Also suggests some extra swaps for words with exactly 4 or 5 characters.
    fn adjacent_swap_suggest(&self, word: &str, out: &mut Vec<String>) {
        // Nuspell early-returns on this condition but I don't think that's necessary.
        debug_assert!(!word.is_empty());

        let buffer = &mut String::from(word);
        let mut chars = word.char_indices().peekable();
        while let Some(((idx1, ch1), (_idx2, ch2))) = chars.next().zip(chars.peek()) {
            swap_adjacent_chars(buffer, idx1, ch1, *ch2);
            self.add_suggestion_if_correct(&*buffer, out);
            swap_adjacent_chars(buffer, idx1, *ch2, ch1);
            debug_assert_eq!(word, &*buffer);
        }

        // For words with exactly 4 or 5 characters try some additional swaps.
        let mut chars = word.char_indices();
        let Some((idx1, ch1)) = chars.next() else {
            return;
        };
        let Some((idx2, ch2)) = chars.next() else {
            return;
        };
        let Some((idx3, ch3)) = chars.next() else {
            return;
        };
        let Some((idx4, ch4)) = chars.next() else {
            return;
        };
        let Some((_idx5, ch5)) = chars.next() else {
            // Word has 4 characters. Try a double swap: the first two and last two characters.
            swap_adjacent_chars(buffer, idx1, ch1, ch2); // swap 1 & 2
            swap_adjacent_chars(buffer, idx3, ch3, ch4); // swap 3 & 4
            self.add_suggestion_if_correct(&*buffer, out);
            swap_adjacent_chars(buffer, idx1, ch2, ch1); // undo 1 & 2
            swap_adjacent_chars(buffer, idx3, ch4, ch3); // undo 3 & 4
            debug_assert_eq!(word, &*buffer);
            return;
        };
        if chars.next().is_none() {
            // Word has 5 characters. Try two different double swaps: the first two and last two
            // and then the second and third and last two.
            swap_adjacent_chars(buffer, idx1, ch1, ch2); // swap 1 & 2
            swap_adjacent_chars(buffer, idx4, ch4, ch5); // swap 4 & 5
            self.add_suggestion_if_correct(&*buffer, out);
            swap_adjacent_chars(buffer, idx1, ch2, ch1); // undo 1 & 2
            swap_adjacent_chars(buffer, idx2, ch2, ch3); // swap 2 & 3
            self.add_suggestion_if_correct(&*buffer, out);
            swap_adjacent_chars(buffer, idx2, ch3, ch2); // undo 2 & 3
            swap_adjacent_chars(buffer, idx4, ch5, ch4); // undo 4 & 5
            debug_assert_eq!(word, &*buffer);
        };
    }

    /// Suggests swapping two non-adjacent characters in the word.
    fn distant_swap_suggest(&self, word: &str, out: &mut Vec<String>) {
        debug_assert!(!word.is_empty());
        let mut remaining_attempts = self.max_attempts_for_long_alogs(word);
        let buffer = &mut String::from(word);

        for (idx1, ch1) in word.char_indices() {
            for (mut idx2, ch2) in word[idx1..].char_indices().skip(1) {
                // Adjust idx2 so it's an absolute index into word.
                idx2 += idx1;
                if remaining_attempts == 0 {
                    return;
                }
                remaining_attempts -= 1;
                idx2 = swap_distant_chars(buffer, idx1, ch1, idx2, ch2);
                self.add_suggestion_if_correct(&*buffer, out);
                swap_distant_chars(buffer, idx1, ch2, idx2, ch1);
                debug_assert_eq!(word, &*buffer);
            }
        }
    }

    /// Suggests replacing characters in the word with the keys around them on the keyboard.
    ///
    /// Also suggests uppercasing individual characters - this suggests that you meant to hit
    /// shift while typing a character.
    fn keyboard_suggest(&self, word: &str, out: &mut Vec<String>) {
        let kb = &self.checker.aff.keyboard_closeness;
        let mut buffer = String::from(word);

        for (idx, word_ch) in word.char_indices() {
            let mut uppercase = word_ch.to_uppercase();
            if !(uppercase.len() == 1 && uppercase.next() == Some(word_ch)) {
                // Are the indices correct here?
                buffer.truncate(idx);
                buffer.extend(word_ch.to_uppercase());
                buffer.extend(word[idx..].chars().skip(1));
                self.add_suggestion_if_correct(&buffer, out);
                buffer.truncate(idx);
                buffer.push_str(&word[idx..]);
                debug_assert_eq!(word, &buffer);
            }

            for (match_idx, _) in kb.match_indices(word_ch) {
                if let Some(prev_kb_ch) =
                    kb[..match_idx].chars().next_back().filter(|ch| *ch != '|')
                {
                    buffer.remove(idx);
                    buffer.insert(idx, prev_kb_ch);
                    self.add_suggestion_if_correct(&buffer, out);
                    buffer.remove(idx);
                    buffer.insert(idx, word_ch);
                    debug_assert_eq!(word, &buffer);
                }

                if let Some(next_kb_ch) = kb[..match_idx].chars().next().filter(|ch| *ch != '|') {
                    buffer.remove(idx);
                    buffer.insert(idx, next_kb_ch);
                    self.add_suggestion_if_correct(&buffer, out);
                    buffer.remove(idx);
                    buffer.insert(idx, word_ch);
                    debug_assert_eq!(word, &buffer);
                }
            }
        }
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

    /// Suggests removing two duplicate characters in a pattern of interspersed characters.
    ///
    /// This suggestion method notices a pattern 'xyxyx' and suggests removing the trailing 'yx'.
    /// ('x' and 'y' are placeholders here - it can be any two characters.)
    fn doubled_two_chars_suggest(&self, word: &str, out: &mut Vec<String>) {
        // To find the 'xyxyx' pattern we set up a sliding window of characters and their byte
        // indices. We shift along the word comparing the elements in that window
        let mut window = [(0, '0'); 5];
        let mut n_chars = 0;
        let mut chars = word.char_indices();
        for (n, (idx, char)) in chars.by_ref().enumerate().take(5) {
            window[n] = (idx, char);
            n_chars = n;
        }
        if n_chars != 4 {
            return;
        }
        for (next_idx, next_char) in chars {
            if window[0].1 == window[2].1
                && window[1].1 == window[3].1
                && window[0].1 == window[4].1
            {
                // This condition is unlikely to be met and is unlikely to occur multiple times
                // in one word. So we don't allocate preemptively outside the loop: allocate a
                // fresh buffer here and don't bother restoring the buffer so it matches `word`.
                // If we decide to pass a `&mut String` buffer for these suggester methods to
                // share this might change.
                let mut buffer = String::from(word);
                buffer.drain(window[3].0..next_idx);
                self.add_suggestion_if_correct(buffer, out);
                // In case we decide to pass a buffer for all suggesters:
                // buffer.insert_str(window[3].0, &word[window[1].0..window[3].0]);
                // debug_assert_eq!(&buffer, word);
            }
            // Slide the window to the next character in the word, discarding the leftmost:
            window.rotate_left(1);
            window[4] = (next_idx, next_char);
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

/// Swaps the two given characters in the given string assuming that they are adjacent.
///
/// Adjacency is asserted in debug builds.
fn swap_adjacent_chars(string: &mut str, idx1: usize, ch1: char, ch2: char) -> usize {
    debug_assert_eq!(string[idx1..].chars().next(), Some(ch1));
    debug_assert_eq!(string[idx1..].chars().nth(1), Some(ch2));

    // Because the characters are adjacent we can simply rewrite the bytes: this will not mess up
    // any other indices into the string. The index of the second character may change if the
    // UTF-8 length of the characters is unequal so we return that index.
    unsafe {
        // PERF: would it be smarter to rotate the slice by whichever is shorter like in
        // `swap_distant_chars`? On the other hand UTF-8 encoding looks very fast.
        let bytes = string.as_bytes_mut();
        // The byte index of the start of the second character after swapping:
        let new_idx2 = idx1 + ch2.len_utf8();
        let end = new_idx2 + ch1.len_utf8();
        ch2.encode_utf8(&mut bytes[idx1..new_idx2]);
        ch1.encode_utf8(&mut bytes[new_idx2..end]);
        new_idx2
    }
}

/// Swaps the given characters at their given byte indices, returning the second character's
/// updated byte index.
///
/// This is more general than `swap_adjacent_chars` which can be done more simply. To accommodate
/// swapping characters of different UTF-8 lengths we need to rotate the bytes which is
/// unnecessary when swapping adjacent chars.
///
/// `idx1` must not equal `idx2`. To eliminate duplicate work the caller passes in the chars at
/// `idx1` and `idx2` but these values must be equivalent to `string[idx..].chars().next()` for
/// `idx1` and `idx2`. These requirements are asserted in debug builds.
fn swap_distant_chars(string: &mut str, idx1: usize, ch1: char, idx2: usize, ch2: char) -> usize {
    use core::cmp::Ordering::*;

    debug_assert_ne!(idx1, idx2);

    let len1 = ch1.len_utf8();
    let len2 = ch2.len_utf8();
    let end = idx2 + len2;
    match len1.cmp(&len2) {
        Equal => {
            // If the two characters have the same length then we don't need to move any
            // characters that come in between. Simply swap the values:
            unsafe {
                let ptr = string.as_mut_ptr();
                // This is essentially `core::mem::swap` of the two subslices containing the
                // character bytes. (In fact `mem::swap` is implemented in terms of
                // `ptr::swap_nonoverlapping`.)
                core::ptr::swap_nonoverlapping(ptr.add(idx1), ptr.add(idx2), len1);
            }
            // Since the characters have the same lengths the indices don't change:
            idx2
        }
        // For `Less` and `Greater` branches we want to rotate right or left depending on which
        // character takes more bytes in UTF-8. This shifts the bytes of the characters between
        // the ones we are swapping. It messes up the bytes of the characters we're swapping but
        // we don't care because we overwrite them with `char::encode_utf8` anyways.
        Less => {
            // Guaranteed to not underflow because `len1 < len2`.
            let rotation = len2 - len1;
            unsafe {
                let bytes = string.as_bytes_mut();
                bytes[idx1..end].rotate_right(rotation);
                let new_idx2 = idx2 + rotation;
                ch2.encode_utf8(&mut bytes[idx1..idx1 + len2]);
                ch1.encode_utf8(&mut bytes[new_idx2..new_idx2 + len1]);
                new_idx2
            }
        }
        Greater => {
            // Guaranteed to not underflow because `len1 > len2`.
            let rotation = len1 - len2;
            unsafe {
                let bytes = string.as_bytes_mut();
                bytes[idx1..end].rotate_left(rotation);
                let new_idx2 = idx2 - rotation;
                ch2.encode_utf8(&mut bytes[idx1..idx1 + len2]);
                ch1.encode_utf8(&mut bytes[new_idx2..new_idx2 + len1]);
                new_idx2
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        alloc::{string::ToString, vec},
        Dictionary, EN_US,
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

    #[test]
    fn swap_adjacent_chars_test() {
        fn swap_adjacent_chars(word: &str, idx: usize) -> String {
            let mut buffer = String::from(word);
            let mut chars = word[idx..].chars();
            let ch1 = chars.next().unwrap();
            let ch2 = chars.next().unwrap();
            super::swap_adjacent_chars(buffer.as_mut_str(), idx, ch1, ch2);
            buffer
        }

        assert_eq!(swap_adjacent_chars("exmaple", 2), "example".to_string());
        assert_eq!(swap_adjacent_chars("épée", 2), "éépe".to_string());
    }

    #[test]
    fn swap_distant_chars_test() {
        fn swap_distant_chars(word: &str, idx1: usize, idx2: usize) -> String {
            let mut buffer = String::from(word);
            let ch1 = word[idx1..].chars().next().unwrap();
            let ch2 = word[idx2..].chars().next().unwrap();
            super::swap_distant_chars(buffer.as_mut_str(), idx1, ch1, idx2, ch2);
            buffer
        }

        assert_eq!(swap_distant_chars("example", 1, 4), "epamxle".to_string());
        assert_eq!(swap_distant_chars("iclaér", 0, 4), "éclair".to_string());
        assert_eq!(swap_distant_chars("éclair", 0, 5), "iclaér".to_string());
        assert_eq!(swap_distant_chars("épée", 0, 3), "épée".to_string());
    }

    fn suggest(dict: &Dictionary, word: &str) -> Vec<String> {
        let mut suggestions = Vec::new();
        dict.suggest(word, &mut suggestions);
        suggestions
    }

    #[test]
    fn empty_suggest() {
        assert!(suggest(&EN_US, "").is_empty());
    }

    #[test]
    fn huge_word_is_skipped() {
        assert!(suggest(&EN_US, &"hello".repeat(MAX_WORD_LEN)).is_empty());
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
        assert!(suggest(&EN_US, "ansi").contains(&"ANSI".to_string()));
    }

    #[test]
    fn extra_char_suggest() {
        assert!(suggest(&EN_US, "adveenture").contains(&"adventure".to_string()));
    }

    #[test]
    fn rep_suggest() {
        // Uses the en_US `REP size cise`. Sounds similar but "cise" is correct here.
        assert!(suggest(&EN_US, "exsize").contains(&"excise".to_string()));
    }

    #[test]
    fn forgotten_char_suggest() {
        assert!(suggest(&EN_US, "helo").contains(&"hello".to_string()));
        assert!(suggest(&EN_US, "wrld").contains(&"world".to_string()));
    }

    #[test]
    fn wrong_char_suggest() {
        let suggestions = suggest(&EN_US, "faver");
        assert!(suggestions.contains(&"fiver".to_string()));
        //                              ^
        assert!(suggestions.contains(&"faker".to_string()));
        //                               ^
        assert!(suggestions.contains(&"favor".to_string()));
        //                                ^
    }

    #[test]
    fn keyboard_suggest() {
        let aff = r#"
        KEY qwertyuiop|asdfghjkl|zxcvbnm
        "#;
        let dic = r#"1
        dream
        "#;
        let dict = Dictionary::new(aff, dic).unwrap();

        assert!(suggest(&dict, "dteam").contains(&"dream".to_string()));
        assert!(suggest(&dict, "dresm").contains(&"dream".to_string()));
        assert!(!suggest(&dict, "dredm").contains(&"dream".to_string()));
    }

    #[test]
    fn adjacent_swap_suggest() {
        // Main part of `adjacent_swap_suggest`: swap any two characters.
        assert!(suggest(&EN_US, "exmaple").contains(&"example".to_string()));
        assert!(suggest(&EN_US, "examlpe").contains(&"example".to_string()));
        // The part at the end of the function: extra swaps for words with 4 or 5 characters.
        // 4 characters double swap - first and last two characters:
        assert!(suggest(&EN_US, "ende").contains(&"need".to_string()));
        // 5 characters double swap - first and last two characters:
        assert!(suggest(&EN_US, "rdema").contains(&"dream".to_string()));
        // 5 characters double swap - second and third and last two characters:
        assert!(suggest(&EN_US, "derma").contains(&"dream".to_string()));
    }

    #[test]
    fn distant_swap_suggest() {
        assert!(suggest(&EN_US, "epamxle").contains(&"example".to_string()));
    }

    #[test]
    fn doubled_two_chars_suggest() {
        assert!(suggest(&EN_US, "bananana").contains(&"banana".to_string()));
        assert!(suggest(&EN_US, "exexecute").contains(&"execute".to_string()));
    }
}
