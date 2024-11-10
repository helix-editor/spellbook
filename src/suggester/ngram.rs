// The parent module covers suggestions made by editing the input word (for example swapping two
// characters.)  This module instead covers "ngram suggestions" - a fancier and more expensive
// procedure.
//
// The basic idea of ngram suggestion is to find words in the dictionary similar to the input
// word. To do that we try to filter down the wordlist words in a multi step process.
//
// 1. Find 100 stems in the word list with the highest "ngram similarity" score to the input word.
// 2. Expand the prefixes and suffixes for those 100 stems and find the 200 expanded words with
//    the highest ngram similarity score to the input word.
// 3. Re-score the (up to) 200 best candidates based on weighted ngram similarity and other
//    bespoke metrics.
// 4. Push the most promising candidates to the `out` vec.
//
// Note that this is **very** expensive compared to regular edit based suggestions since we need
// to iterate on the word list and expand affixes.
//
// Ngram suggestions are also criticized as not very smart:
// <https://battlepenguin.com/tech/aspell-and-hunspell-a-tale-of-two-spell-checkers/>. Ngram
// suggestions are implemented for compatibility with Nuspell/Hunspell but we could consider
// adding other strategies as well, for example looking at the Aspell code.

use core::hash::BuildHasher;

use crate::alloc::{collections::BinaryHeap, string::String, vec::Vec};

use crate::aff::{CaseHandling, HIDDEN_HOMONYM_FLAG, MAX_SUGGESTIONS};
use crate::{FlagSet, Stem, FULL_WORD};

use super::Suggester;

// For ngram suggestions we'll be switching to UTF-32. UTF-32 uses 32-bit integers to represent
// every char.
//
// Compare to UTF-8 - the representation of `String` and `str` - in which a character could be
// represented by one through four bytes.
//
// UTF-32 is handy because indices are intuitive. `utf32_str[3]` is the third character. The same
// isn't true of UTF-8 - you index into the bytes so `utf8_str[3]` could be right in the middle of
// the bytes used to represent a character.
//
// `String` is a newtype wrapper around a `Vec<u8>` which is asserted to contain valid UTF-8. In
// contrast we won't use a newtype wrapper for our Utf32String below since any sequence of
// `char`s is valid UTF-32.
//
// This is getting off-topic but UTF-8 is generally preferred because it has good compression -
// for ASCII (which very common) you only need a byte to represent a character. UTF-32 strings
// take a constant 4 bytes per character which is relatively expensive.
type Utf32String = Vec<char>;
type Utf32Str = [char];

macro_rules! has_flag {
    ( $flags:expr, $flag:expr ) => {{
        match $flag {
            Some(flag) => $flags.contains(&flag),
            None => false,
        }
    }};
}

/// This struct is used as a wrapper for other data (for example stem+flagset) to organize a
/// min-heap with BinaryHeap. (`BinaryHeap` from the standard library is a max-heap and you need
/// to reverse the Ord of the type to use it as a min-heap.)
#[derive(Debug, PartialEq, Eq)]
struct MinScored<T: PartialEq + Eq> {
    score: isize,
    inner: T,
}

impl<T: PartialEq + Eq> Ord for MinScored<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.score.cmp(&other.score).reverse()
    }
}

impl<T: PartialEq + Eq> PartialOrd<Self> for MinScored<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, S: BuildHasher> Suggester<'a, S> {
    pub(super) fn ngram_suggest(&self, word: &str, out: &mut Vec<String>) {
        // First step: find 100 stems in the word list with the best ngram score.

        let wrong_word: Utf32String = word.chars().collect();
        let mut wide_buf = Vec::new();
        let mut roots = BinaryHeap::with_capacity(100);
        let mut stem_utf32 = Vec::new();
        for (stem_utf8, flagset) in self.checker.words.iter() {
            if has_flag!(flagset, self.checker.aff.options.forbidden_word_flag)
                || has_flag!(flagset, self.checker.aff.options.no_suggest_flag)
                || has_flag!(flagset, self.checker.aff.options.only_in_compound_flag)
                || flagset.contains(&HIDDEN_HOMONYM_FLAG)
            {
                continue;
            }
            // Convert the dictionary stem to UTF-32.
            stem_utf32.clear();
            stem_utf32.extend(stem_utf8.as_ref().chars());
            let mut score = left_common_substring_length(
                &self.checker.aff.options.case_handling,
                &wrong_word,
                &stem_utf32,
            ) as isize;

            wide_buf.clear();
            self.checker
                .aff
                .options
                .case_handling
                .lowercase_into_utf32(stem_utf8.as_ref(), &mut wide_buf);
            score += ngram_similarity_longer_worse(3, &wrong_word, &wide_buf);

            let root = MinScored {
                score,
                inner: (stem_utf8, flagset),
            };
            if roots.len() != 100 {
                roots.push(root);
            } else if roots.peek().is_some_and(|entry| score > entry.score) {
                // The heap has hit capacity. Drop the lowest scoring root and push this new
                // higher scored root.
                roots.pop();
                roots.push(root);
            }
        }

        // Calculate a somewhat low threshold score so that we can ignore bad suggestions in the
        // next steps.
        let mut threshold = 0isize;
        for k in 1..=3 {
            let mangled_word = &mut wide_buf;
            mangled_word.clear();
            mangled_word.extend_from_slice(&wrong_word);
            let mut i = k;
            while i < mangled_word.len() {
                mangled_word[i] = '*';
                i += 4;
            }
            threshold += ngram_similarity_any_mismatch(wrong_word.len(), &wrong_word, mangled_word);
        }

        threshold /= 3;

        // Step two: expand the affixes for these wordlist entries, gathering the 200 highest
        // scoring candidates.

        let mut expanded_list = Vec::new();
        let mut expanded_cross_affix = Vec::new();
        let mut expanded_word_utf32 = Vec::new();
        let mut guess_words = BinaryHeap::new();

        for MinScored {
            inner: (stem, flags),
            ..
        } in roots
        {
            expanded_cross_affix.clear();
            self.expand_stem_for_ngram(
                stem,
                flags,
                word,
                &mut expanded_list,
                &mut expanded_cross_affix,
            );
            for expanded_word_utf8 in expanded_list.drain(..) {
                expanded_word_utf32.clear();
                expanded_word_utf32.extend(expanded_word_utf8.chars());

                let mut score = left_common_substring_length(
                    &self.checker.aff.options.case_handling,
                    &wrong_word,
                    &expanded_word_utf32,
                ) as isize;

                let lower_expanded_word = &mut wide_buf;
                lower_expanded_word.clear();
                self.checker
                    .aff
                    .options
                    .case_handling
                    .lowercase_into_utf32(&expanded_word_utf8, lower_expanded_word);
                score += ngram_similarity_any_mismatch(
                    wrong_word.len(),
                    &wrong_word,
                    lower_expanded_word,
                );

                if score < threshold {
                    continue;
                }

                // Nuspell stores the UTF-32 word in `guess_words`, but then later converts from
                // UTF-32 into UTF-8 when pushing into `out`. For our sake it's easier to store
                // the UTF-8 instead and avoid the conversion later.
                let guess_word = MinScored {
                    score,
                    inner: expanded_word_utf8,
                };
                if guess_words.len() != 200 {
                    guess_words.push(guess_word);
                } else if guess_words.peek().is_some_and(|entry| score > entry.score) {
                    guess_words.pop();
                    guess_words.push(guess_word);
                }
            }
        }

        // Step three: rescore these up to 200 potential matches based on a weighted ngram
        // calculation and other bespoke measurements.

        // Scratchpad vector used for calculating longest common subsequences. See
        // `longest_common_subsequence_length`.
        let mut lcs_state = Vec::new();
        // Nuspell questions whether or not the heap needs to be sorted before iterating.
        // For now, they sort the heap. I think Nuspell is correct to do so because the `break`
        // below could cause a different end behavior based on whether we're iterating on a sorted
        // or unsorted vec.
        let mut guess_words = guess_words.into_sorted_vec();
        for MinScored {
            score,
            inner: guess_word,
        } in guess_words.iter_mut()
        {
            let lower_guess_word = &mut wide_buf;
            lower_guess_word.clear();
            self.checker
                .aff
                .options
                .case_handling
                .lowercase_into_utf32(guess_word, lower_guess_word);

            let lcs =
                longest_common_subsequence_length(&wrong_word, lower_guess_word, &mut lcs_state);

            if wrong_word.len() == lower_guess_word.len() && wrong_word.len() == lcs {
                *score += 2000;
                break;
            }

            let mut ngram2 =
                ngram_similarity_any_mismatch_weighted(2, &wrong_word, lower_guess_word);
            ngram2 += ngram_similarity_any_mismatch_weighted(2, lower_guess_word, &wrong_word);
            let ngram4 = ngram_similarity_any_mismatch(4, &wrong_word, lower_guess_word);
            let left_common = left_common_substring_length(
                &self.checker.aff.options.case_handling,
                &wrong_word,
                lower_guess_word,
            );
            let (num_eq_chars_same_pos, eq_char_is_swapped) =
                count_eq_at_same_pos(&wrong_word, lower_guess_word);

            *score = 2 * lcs as isize;
            *score -= (wrong_word.len() as isize - lower_guess_word.len() as isize).abs();
            *score += left_common as isize + ngram2 + ngram4;
            if num_eq_chars_same_pos != 0 {
                *score += 1;
            }
            if eq_char_is_swapped {
                *score += 10;
            }

            if 5 * ngram2
                < ((wrong_word.len() + lower_guess_word.len())
                    * (10 - self.checker.aff.options.max_diff_factor as usize))
                    as isize
            {
                *score -= 1000;
            }
        }

        // We've updated the scores (`iter_mut` above) so we need to re-sort the Vec.
        // Note that because of `MinScored<T>`'s `Ord` implementation the Vec is ordered by
        // score descending. (Normally a sort would be ascending.)
        guess_words.sort_unstable();

        // Step four: push the most promising of the candidates to `out`.

        let be_more_selective = guess_words.first().is_some_and(|guess| guess.score > 1000);
        let old_num_suggestions = out.len();
        let max_suggestions = MAX_SUGGESTIONS
            .min(old_num_suggestions + self.checker.aff.options.max_ngram_suggestions as usize);
        for MinScored {
            score,
            inner: guess_word,
        } in guess_words.into_iter()
        {
            if out.len() == max_suggestions {
                break;
            }
            // Note that we are iterating in descending score order, so this sets a minimum.
            if be_more_selective && score <= 1000 {
                break;
            }
            if score < -100
                && (old_num_suggestions != out.len() || self.checker.aff.options.only_max_diff)
            {
                break;
            }
            // Nuspell is converting back to UTF-8 but we store the `guess_word` in UTF-8 form.
            // I think Nuspell only carries UTF-32 because of templates allowing easy conversion
            // to lowercase. In Spellbook's case we need an explicit function for this and we
            // already have one for UTF-8, so it's easier to carry UTF-8. It's nearly always less
            // memory plus we save a conversion to UTF-8 right here:
            if out
                .iter()
                .any(|sug| contains_subslice(guess_word.as_bytes(), sug.as_bytes()))
            {
                if score < -100 {
                    break;
                } else {
                    continue;
                }
            }
            out.push(guess_word);
        }
    }

    fn expand_stem_for_ngram(
        &self,
        stem: &Stem,
        flags: &FlagSet,
        word: &str,
        expanded_list: &mut Vec<String>,
        cross_affix: &mut Vec<bool>,
    ) {
        expanded_list.clear();
        cross_affix.clear();

        if !has_flag!(flags, self.checker.aff.options.need_affix_flag) {
            expanded_list.push(String::from(stem.as_ref()));
            cross_affix.push(false);
        }

        if flags.is_empty() {
            return;
        }

        // TODO: investigate collecting `all_flags` (like we do for compounds IIRC) on the
        // prefixes and suffixes tables to see if we can disqualify flagsets faster?

        for suffix in self.checker.aff.suffixes.iter() {
            // Nuspell:
            // if (!cross_valid_inner_outer(flags, suffix))
            // 	continue;
            if !flags.contains(&suffix.flag) {
                continue;
            }
            if !self.checker.is_outer_affix_valid::<_, FULL_WORD>(suffix) {
                continue;
            }
            if self.checker.is_circumfix(suffix) {
                continue;
            }
            // Nuspell has a todo here:
            // > Suffixes marked with needaffix or circumfix should not just be skipped as we can
            // > later add prefix. This is not handled in hunspell, too.
            if suffix
                .strip
                .as_ref()
                .is_some_and(|suf| !stem.as_str().ends_with(suf))
            {
                continue;
            }
            if !suffix.condition_matches(stem.as_str()) {
                continue;
            }
            if !suffix.add.is_empty() && !word.ends_with(&suffix.add) {
                continue;
            }

            let expanded = suffix.to_derived(stem.as_str());
            expanded_list.push(expanded);
            cross_affix.push(suffix.crossproduct);
        }

        // Expand crossproduct words - prefixes for suffix-expanded words marked with
        // `crossproduct: true`.
        for i in 0..expanded_list.len() {
            if !cross_affix[i] {
                continue;
            }

            for prefix in self.checker.aff.prefixes.iter() {
                let suffixed_stem = &expanded_list[i];
                // if (!cross_valid_inner_outer(flags, prefix))
                // 	continue;
                if !flags.contains(&prefix.flag) {
                    continue;
                }
                if !self.checker.is_outer_affix_valid::<_, FULL_WORD>(prefix) {
                    continue;
                }
                if self.checker.is_circumfix(prefix) {
                    continue;
                }
                if prefix
                    .strip
                    .as_ref()
                    .is_some_and(|pre| !suffixed_stem.starts_with(pre))
                {
                    continue;
                }
                if !prefix.condition_matches(suffixed_stem) {
                    continue;
                }
                if !prefix.add.is_empty() && !word.starts_with(&prefix.add) {
                    continue;
                }

                let expanded = prefix.to_derived(stem.as_str());
                expanded_list.push(expanded);
            }
        }

        for prefix in self.checker.aff.prefixes.iter() {
            // Nuspell:
            // if (!cross_valid_inner_outer(flags, prefix))
            // 	continue;
            if !flags.contains(&prefix.flag) {
                continue;
            }
            if !self.checker.is_outer_affix_valid::<_, FULL_WORD>(prefix) {
                continue;
            }
            if self.checker.is_circumfix(prefix) {
                continue;
            }
            if prefix
                .strip
                .as_ref()
                .is_some_and(|pre| !stem.as_str().starts_with(pre))
            {
                continue;
            }
            if !prefix.condition_matches(stem.as_str()) {
                continue;
            }
            if !prefix.add.is_empty() && !word.starts_with(&prefix.add) {
                continue;
            }

            let expanded = prefix.to_derived(stem.as_str());
            expanded_list.push(expanded);
        }
    }
}

fn left_common_substring_length(
    case_handling: &CaseHandling,
    left: &Utf32Str,
    right: &Utf32Str,
) -> usize {
    if left.is_empty() || right.is_empty() {
        return 0;
    }

    if left[0] != right[0] && !case_handling.is_char_eq_lowercase(left[0], right[0]) {
        return 0;
    }

    index_of_mismatch(&left[1..], &right[1..])
        .map(|idx| idx + 1)
        .unwrap_or(left.len())
}

fn index_of_mismatch<T: Eq>(left: &[T], right: &[T]) -> Option<usize> {
    left.iter()
        .enumerate()
        .find_map(|(idx, l)| match right.get(idx) {
            Some(r) if r == l => None,
            _ => Some(idx),
        })
}

fn ngram_similarity_longer_worse(n: usize, left: &Utf32Str, right: &Utf32Str) -> isize {
    if right.is_empty() {
        return 0;
    }
    let mut score = ngram_similarity(n, left, right);
    let d = (left.len() as isize - right.len() as isize) - 2;
    if d > 0 {
        score -= d;
    }
    score
}

// Nuspell calls this `ngram_similarity_low_level`.
fn ngram_similarity(n: usize, left: &Utf32Str, right: &Utf32Str) -> isize {
    let n = n.min(left.len());
    let mut score = 0;

    for k in 1..=n {
        let mut k_score = 0;
        for i in 0..=left.len() - k {
            let kgram = &left[i..i + k];
            if contains_subslice(right, kgram) {
                k_score += 1;
            }
        }
        score += k_score;
        if k_score < 2 {
            break;
        }
    }

    score
}

fn contains_subslice<T: Eq>(slice: &[T], subslice: &[T]) -> bool {
    if subslice.len() > slice.len() {
        return false;
    }

    let window = slice.len() - subslice.len();
    for i in 0..=window {
        if slice[i..].starts_with(subslice) {
            return true;
        }
    }

    false
}

fn ngram_similarity_any_mismatch(n: usize, left: &Utf32Str, right: &Utf32Str) -> isize {
    if right.is_empty() {
        return 0;
    }
    let mut score = ngram_similarity(n, left, right);
    let d = (right.len() as isize - left.len() as isize).abs() - 2;
    if d > 0 {
        score -= d;
    }
    score
}

// Nuspell returns an isize.
fn longest_common_subsequence_length<T: Eq>(
    left: &[T],
    right: &[T],
    state_buffer: &mut Vec<usize>,
) -> usize {
    state_buffer.clear();
    state_buffer.resize(right.len(), 0);

    let mut row1_prev = 0;
    for l in left.iter() {
        row1_prev = 0;
        let mut row2_prev = 0;
        for j in 0..right.len() {
            let row1_current = state_buffer[j];
            let row2_current = &mut state_buffer[j];
            *row2_current = if *l == right[j] {
                row1_prev + 1
            } else {
                row1_current.max(row2_prev)
            };
            row1_prev = row1_current;
            row2_prev = *row2_current;
        }
        row1_prev = row2_prev;
    }

    row1_prev
}

fn ngram_similarity_any_mismatch_weighted(n: usize, left: &Utf32Str, right: &Utf32Str) -> isize {
    if right.is_empty() {
        return 0;
    }
    let mut score = ngram_similarity_weighted(n, left, right);
    let d = (right.len() as isize - left.len() as isize).abs() - 2;
    if d > 0 {
        score -= d;
    }
    score
}

fn ngram_similarity_weighted(n: usize, left: &Utf32Str, right: &Utf32Str) -> isize {
    let n = n.min(left.len());
    let mut score = 0;

    for k in 1..=n {
        let mut k_score = 0;
        for i in 0..=left.len() - k {
            let kgram = &left[i..i + k];
            if contains_subslice(right, kgram) {
                k_score += 1;
            } else {
                k_score -= 1;
                if i == 0 || i == left.len() - k {
                    k_score -= 1;
                }
            }
        }
        score += k_score;
    }

    score
}

fn count_eq_at_same_pos<T: Eq + Copy>(left: &[T], right: &[T]) -> (usize, bool) {
    let n = left.len().min(right.len());
    let count = left
        .iter()
        .zip(right.iter())
        .filter(|(l, r)| l == r)
        .count();

    let mut is_swap = false;
    // Only two characters are not equal. Check if they were swapped.
    if left.len() == right.len() && n - count == 2 {
        let mut first_mismatch = None;
        for (l, r) in left.iter().zip(right.iter()) {
            if l != r {
                if let Some((l1, r1)) = first_mismatch {
                    is_swap = l1 == r && r1 == l;
                    break;
                }
                first_mismatch = Some((l, r));
            }
        }
    }

    (count, is_swap)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn index_of_mismatch_test() {
        assert_eq!(index_of_mismatch(b"abcd", b"abcd"), None);
        assert_eq!(index_of_mismatch(b"abcd", b"abxy"), Some(2));
        assert_eq!(index_of_mismatch(b"abcd", b"abc"), Some(3));
        assert_eq!(index_of_mismatch(b"abc", b"abcd"), None);
    }

    #[test]
    fn contains_subslice_test() {
        assert!(contains_subslice(b"abcd", b"abcd"));
        assert!(contains_subslice(b"abcd", b"abc"));
        assert!(contains_subslice(b"abcd", b"bcd"));
        assert!(contains_subslice(b"abcd", b"b"));
    }

    #[test]
    fn nagrm_similarity_test() {
        // Rebuilding the Spellchecker:
        // > ngram(3, 'actually', 'akchualy')
        // > 11 = a, c, u, a, l, l, y, ua, al, ly, ual
        let left: Utf32String = "actually".chars().collect();
        let right: Utf32String = "akchualy".chars().collect();
        assert_eq!(ngram_similarity(3, &left, &right), 11);
    }

    #[test]
    fn longest_common_subsequence_length_test() {
        let mut state_buffer = Vec::new();
        assert_eq!(
            longest_common_subsequence_length(b"aaa", b"aaa", &mut state_buffer),
            3
        );
        assert_eq!(
            longest_common_subsequence_length(b"aaaaa", b"bbbaa", &mut state_buffer),
            2
        );
    }

    #[test]
    fn count_eq_at_same_pos_test() {
        assert_eq!(count_eq_at_same_pos(b"abcd", b"abcd"), (4, false));
        assert_eq!(count_eq_at_same_pos(b"abcd", b"acbd"), (2, true));
    }
}
