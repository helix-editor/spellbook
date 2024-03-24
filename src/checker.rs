use core::hash::BuildHasher;

use crate::{
    aff::{AffData, Affix, AffixKind, Pfx, Prefix, Sfx, Suffix, HIDDEN_HOMONYM_FLAG},
    alloc::{borrow::Cow, string::String},
    stdx::is_some_and,
    AffixingMode, FlagSet,
};

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

    fn spell_casing(&self, word: &'a str) -> Option<&'a FlagSet> {
        // Classify the casing
        // For lowercase, camel & pascal `check_word`
        // For uppercase, spell_casing_upper
        // For title, spell_casing_title

        match classify_casing(word) {
            Casing::None | Casing::Camel | Casing::Pascal => {
                self.check_word(word, Forceucase::default(), HiddenHomonym::default())
            }
            Casing::All => None,  // spell_casing_upper
            Casing::Init => None, // spell_casing_title
        }
    }

    fn check_word(
        &self,
        word: &'a str,
        allow_bad_forceucase: Forceucase,
        hidden_homonym: HiddenHomonym,
    ) -> Option<&'a FlagSet> {
        if let Some(flags) = self.check_simple_word(word, hidden_homonym) {
            return Some(flags);
        }

        self.check_compound(word, allow_bad_forceucase)
            .map(|result| result.flags)
    }

    fn check_simple_word(
        &self,
        word: &'a str,
        hidden_homonym: HiddenHomonym,
    ) -> Option<&'a FlagSet> {
        for flags in self.aff.words.get_all(word) {
            if is_some_and(self.aff.options.need_affix_flag, |flag| {
                flags.contains(&flag)
            }) {
                continue;
            }
            if is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                flags.contains(&flag)
            }) {
                continue;
            }
            if hidden_homonym.skip() && flags.contains(&HIDDEN_HOMONYM_FLAG) {
                continue;
            }
            return Some(flags);
        }

        if let Some(form) = self.strip_suffix_only(word, AffixingMode::default(), hidden_homonym) {
            return Some(form.flags);
        }

        if let Some(form) = self.strip_prefix_only(word, AffixingMode::default(), hidden_homonym) {
            return Some(form.flags);
        }

        if let Some(form) =
            self.strip_prefix_then_suffix_commutative(word, AffixingMode::default(), hidden_homonym)
        {
            return Some(form.flags);
        }

        // TODO: rest of check_simple_word:

        if self.aff.options.complex_prefixes {
            // strip_prefix_then_prefix
            // strip_suffix_then_2_prefixes
            // strip_prefix_suffix_prefix
            // strip_2_prefixes_then_suffix (slow and unused, commented out)
            todo!()
        } else {
            if let Some(form) = self.strip_suffix_then_suffix(word, hidden_homonym) {
                return Some(form.flags);
            }
            // strip_prefix_then_2_suffixes
            // strip_suffix_prefix_suffix
            // strip_2_suffixes_then_prefix (slow and unused, commented out)
        }

        None
    }

    fn check_compound(
        &self,
        _word: &str,
        _allow_bad_forceucase: Forceucase,
    ) -> Option<CompoundingResult<'a>> {
        // TODO: compounding
        None
    }

    // TODO: experiment with const generics to replace the affixing mode

    fn strip_suffix_only(
        &self,
        word: &'a str,
        mode: AffixingMode,
        hidden_homonym: HiddenHomonym,
    ) -> Option<AffixForm<'a>> {
        for suffix in self.aff.suffixes.affixes_of(word) {
            if !self.is_outer_affix_valid(suffix, mode) {
                continue;
            }

            if !suffix.add.is_empty()
                && mode == AffixingMode::AtCompoundEnd
                && is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                    suffix.flags.contains(&flag)
                })
            {
                continue;
            }

            if self.is_circumfix(suffix) {
                continue;
            }

            let stem = suffix.to_stem(word);

            if !suffix.condition_matches(&stem) {
                continue;
            }

            for flags in self.aff.words.get_all(stem.as_ref()) {
                // Nuspell:
                // if (!cross_valid_inner_outer(word_flags, e))
                // 	continue;
                if !flags.contains(&suffix.flag) {
                    continue;
                }

                if mode == AffixingMode::FullWord
                    && is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                        suffix.flags.contains(&flag)
                    })
                {
                    continue;
                }

                if hidden_homonym.skip() && flags.contains(&HIDDEN_HOMONYM_FLAG) {
                    continue;
                }

                if !self.is_valid_inside_compound(flags, mode)
                    && !self.is_valid_inside_compound(&suffix.flags, mode)
                {
                    continue;
                }

                return Some(AffixForm {
                    stem,
                    flags,
                    prefixes: Default::default(),
                    suffixes: [Some(suffix), None],
                });
            }
        }

        None
    }

    fn strip_prefix_only(
        &self,
        word: &'a str,
        mode: AffixingMode,
        hidden_homonym: HiddenHomonym,
    ) -> Option<AffixForm<'a>> {
        for prefix in self.aff.prefixes.affixes_of(word) {
            if !self.is_outer_affix_valid(prefix, mode) {
                continue;
            }

            if !prefix.add.is_empty()
                && mode == AffixingMode::AtCompoundEnd
                && is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                    prefix.flags.contains(&flag)
                })
            {
                continue;
            }

            if self.is_circumfix(prefix) {
                continue;
            }

            let stem = prefix.to_stem(word);

            if !prefix.condition_matches(&stem) {
                continue;
            }

            for flags in self.aff.words.get_all(stem.as_ref()) {
                // Nuspell:
                // if (!cross_valid_inner_outer(word_flags, e))
                // 	continue;
                if !flags.contains(&prefix.flag) {
                    continue;
                }

                if mode == AffixingMode::FullWord
                    && is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                        prefix.flags.contains(&flag)
                    })
                {
                    continue;
                }

                if hidden_homonym.skip() && flags.contains(&HIDDEN_HOMONYM_FLAG) {
                    continue;
                }

                if !self.is_valid_inside_compound(flags, mode)
                    && !self.is_valid_inside_compound(&prefix.flags, mode)
                {
                    continue;
                }

                return Some(AffixForm {
                    stem,
                    flags,
                    prefixes: [Some(prefix), None],
                    suffixes: Default::default(),
                });
            }
        }

        None
    }

    // Reversed form of Nuspell's `outer_affix_NOT_valid`
    fn is_outer_affix_valid<K: AffixKind>(&self, affix: &Affix<K>, mode: AffixingMode) -> bool {
        if !K::is_valid(affix, &self.aff.options, mode) {
            return false;
        }

        if is_some_and(self.aff.options.need_affix_flag, |flag| {
            affix.flags.contains(&flag)
        }) {
            return false;
        }

        true
    }

    fn is_circumfix<K: AffixKind>(&self, affix: &Affix<K>) -> bool {
        is_some_and(self.aff.options.circumfix_flag, |flag| {
            affix.flags.contains(&flag)
        })
    }

    fn is_valid_inside_compound(&self, flags: &FlagSet, mode: AffixingMode) -> bool {
        let is_compound = is_some_and(self.aff.options.compound_flag, |flag| flags.contains(&flag));

        match mode {
            AffixingMode::AtCompoundBegin
                if !is_compound
                    && !is_some_and(self.aff.options.compound_begin_flag, |flag| {
                        flags.contains(&flag)
                    }) =>
            {
                false
            }
            AffixingMode::AtCompoundMiddle
                if !is_compound
                    && !is_some_and(self.aff.options.compound_middle_flag, |flag| {
                        flags.contains(&flag)
                    }) =>
            {
                false
            }
            AffixingMode::AtCompoundEnd
                if !is_compound
                    && !is_some_and(self.aff.options.compound_last_flag, |flag| {
                        flags.contains(&flag)
                    }) =>
            {
                false
            }
            _ => true,
        }
    }

    fn strip_prefix_then_suffix_commutative(
        &self,
        word: &'a str,
        mode: AffixingMode,
        hidden_homonym: HiddenHomonym,
    ) -> Option<AffixForm<'a>> {
        // TODO: elide this into `strip_prefix_only`?
        for prefix in self.aff.prefixes.affixes_of(word) {
            if !prefix.crossproduct {
                continue;
            }

            if !Pfx::is_valid(prefix, &self.aff.options, AffixingMode::default()) {
                continue;
            }

            let stem_without_prefix = prefix.to_stem(word);

            if !prefix.condition_matches(&stem_without_prefix) {
                continue;
            }

            // Inlined translation of `strip_pfx_then_sfx_comm_2` from Nuspell.
            let has_needaffix_prefix = is_some_and(self.aff.options.need_affix_flag, |flag| {
                prefix.flags.contains(&flag)
            });
            let is_circumfix_prefix = self.is_circumfix(prefix);

            for suffix in self.aff.suffixes.affixes_of(&stem_without_prefix) {
                if !suffix.crossproduct {
                    continue;
                }

                if !Sfx::is_valid(suffix, &self.aff.options, AffixingMode::default()) {
                    continue;
                }

                // TODO: add a macro around `match` so we don't need `is_some_and`? It's just
                // convenience and yet it's still pretty verbose.
                let has_needaffix_suffix = is_some_and(self.aff.options.need_affix_flag, |flag| {
                    suffix.flags.contains(&flag)
                });

                if has_needaffix_prefix && has_needaffix_suffix {
                    continue;
                }

                if is_circumfix_prefix != self.is_circumfix(suffix) {
                    continue;
                }

                let stem_without_suffix = suffix.to_stem(&stem_without_prefix);

                if !suffix.condition_matches(&stem_without_suffix) {
                    continue;
                }

                for flags in self.aff.words.get_all(stem_without_suffix.as_ref()) {
                    let valid_cross_prefix_outer = !has_needaffix_prefix
                        && flags.contains(&suffix.flag)
                        && (suffix.flags.contains(&prefix.flag) || flags.contains(&prefix.flag));

                    let valid_cross_suffix_outer = !has_needaffix_suffix
                        && flags.contains(&suffix.flag)
                        && (prefix.flags.contains(&suffix.flag) || flags.contains(&suffix.flag));

                    if !valid_cross_prefix_outer && !valid_cross_suffix_outer {
                        continue;
                    }

                    if mode == AffixingMode::FullWord
                        && is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                            flags.contains(&flag)
                        })
                    {
                        continue;
                    }

                    if hidden_homonym.skip() && flags.contains(&HIDDEN_HOMONYM_FLAG) {
                        continue;
                    }

                    if !self.is_valid_inside_compound(flags, mode)
                        && !self.is_valid_inside_compound(&suffix.flags, mode)
                        && !self.is_valid_inside_compound(&prefix.flags, mode)
                    {
                        continue;
                    }

                    return Some(AffixForm {
                        // Unfortunately we need an owned value here. Returning a borrowed Cow
                        // would be returning a reference to `stem_without_prefix`. If
                        // `stem_without_prefix` needs to be owned we would be returning a
                        // reference to a local `String` which would not live long enough.
                        // TODO: can we use some phantomdata/marker trick to get around this and
                        // bind the lifetime of the maybe owned String to the prefix table?
                        stem: stem_without_suffix.into_owned().into(),
                        flags,
                        prefixes: [Some(prefix), None],
                        suffixes: [Some(suffix), None],
                    });
                }
            }
        }

        None
    }

    fn strip_suffix_then_suffix(
        &self,
        word: &'a str,
        hidden_homonym: HiddenHomonym,
    ) -> Option<AffixForm<'a>> {
        // Nuspell notes that this is a fast-lane and doesn't affect correctness.
        if self.aff.suffixes.all_flags.is_empty() {
            return None;
        }

        for outer_suffix in self.aff.suffixes.affixes_of(word) {
            // Another fast lane:
            if !self.aff.suffixes.all_flags.contains(&outer_suffix.flag) {
                continue;
            }

            if !self.is_outer_affix_valid(outer_suffix, AffixingMode::default()) {
                continue;
            }

            if self.is_circumfix(outer_suffix) {
                continue;
            }

            let stem = outer_suffix.to_stem(word);

            if !outer_suffix.condition_matches(&stem) {
                continue;
            }

            // Inline version of strip_sfx_then_sfx_2. Assume `AffixingMode::FullWord` here.
            for inner_suffix in self.aff.suffixes.affixes_of(stem.as_ref()) {
                // Nuspell:
                // if (!cross_valid_inner_outer(word_flags, se2))
                // 	continue;
                if !inner_suffix.flags.contains(&outer_suffix.flag) {
                    continue;
                }

                if !Sfx::is_valid(inner_suffix, &self.aff.options, AffixingMode::FullWord) {
                    continue;
                }
                if self.is_circumfix(inner_suffix) {
                    continue;
                }

                let stem2 = inner_suffix.to_stem(&stem);

                if !inner_suffix.condition_matches(&stem2) {
                    continue;
                }

                for flags in self.aff.words.get_all(stem2.as_ref()) {
                    if !flags.contains(&inner_suffix.flag) {
                        continue;
                    }
                    // Note: assumed `AffixingMode::FullWord`
                    if is_some_and(self.aff.options.only_in_compound_flag, |flag| {
                        inner_suffix.flags.contains(&flag)
                    }) {
                        continue;
                    }

                    if hidden_homonym.skip() && flags.contains(&HIDDEN_HOMONYM_FLAG) {
                        continue;
                    }

                    return Some(AffixForm {
                        stem: stem2.into_owned().into(),
                        flags,
                        prefixes: Default::default(),
                        suffixes: [Some(outer_suffix), Some(inner_suffix)],
                    });
                }
            }
        }

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

// TODO: rename?
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Forceucase {
    ForbidBadForceucase,
    AllowBadForceucase,
}

impl Default for Forceucase {
    fn default() -> Self {
        Self::ForbidBadForceucase
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum HiddenHomonym {
    AcceptHiddenHomonym,
    SkipHiddenHomonym,
}

impl Default for HiddenHomonym {
    fn default() -> Self {
        Self::AcceptHiddenHomonym
    }
}

impl HiddenHomonym {
    #[inline]
    const fn skip(&self) -> bool {
        match self {
            Self::AcceptHiddenHomonym => false,
            Self::SkipHiddenHomonym => true,
        }
    }
}

// Similar to Nuspell's AffixingResult
pub(crate) struct AffixForm<'aff> {
    stem: Cow<'aff, str>,
    flags: &'aff FlagSet,
    // Up to 2 prefixes and/or 2 suffixes allowed.
    prefixes: [Option<&'aff Prefix>; 2],
    suffixes: [Option<&'aff Suffix>; 2],
}

// TODO: docs.
pub(crate) struct CompoundingResult<'a> {
    stem: &'a String,
    flags: &'a FlagSet,
    num_words_modifier: u16,
    num_syllable_modifier: i16,
    affixed_and_modified: bool,
}

#[cfg(test)]
mod test {
    // Note: we need the once_cell crate rather than `core::cell::OnceCell` for the cell to be
    // Sync + Send.
    use once_cell::sync::OnceCell;

    use super::*;
    use crate::*;

    const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");
    const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");

    fn en_us() -> &'static Dictionary<ahash::RandomState> {
        // It's a little overkill to use a real dictionary for unit tests but it compiles so
        // quickly that if we only compile it once it doesn't really slow down the test suite.
        static EN_US: OnceCell<Dictionary<ahash::RandomState>> = OnceCell::new();
        EN_US.get_or_init(|| {
            Dictionary::new_with_hasher(EN_US_DIC, EN_US_AFF, ahash::RandomState::new()).unwrap()
        })
    }

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

    #[test]
    fn check_number_test() {
        assert!(en_us().check("123456789"));
    }

    #[test]
    fn check_exact_word_in_the_wordlist_test() {
        // adventure/DRSMZG (en_US.dic line 11021)
        assert!(en_us().check("adventure"));
    }

    #[test]
    fn check_exact_words_in_the_wordlist_with_break_patterns_test() {
        // en_US uses the default break patterns: `^-`, `-`, `-$`.
        // All of these words are stems in the dictionary.
        assert!(en_us().check("-any"));
        assert!(en_us().check("anyway-anywhere"));
        assert!(en_us().check("ace-"));
    }

    #[test]
    fn check_word_with_single_suffix() {
        // Suffix 'V' from en_US.aff:
        // SFX V N 2
        // SFX V   e     ive        e
        // SFX V   0     ive        [^e]

        // concuss/V (en_US.dic line 17451)
        assert!(en_us().check("concussive"));
        // regenerate/V (en_US.dic line 38722)
        assert!(en_us().check("regenerative"));
    }

    #[test]
    fn check_word_with_single_prefix() {
        // Prefix 'A' from en_US.aff
        // PFX A Y 1
        // PFX A   0     re         .

        // route/ADSG (en_US.dic line 39619)
        assert!(en_us().check("reroute"));
    }

    #[test]
    fn false_prefix_test() {
        // "un" is a prefix in en_US and "drink" is a stem. "drink"'s flags don't allow you to use
        // the "un" prefix though, so this word isn't correct.
        assert!(!en_us().check("undrink"));
    }

    #[test]
    fn check_word_with_prefix_and_suffix() {
        // Prefix 'U' from en_US.aff
        // PFX U Y 1
        // PFX U   0     un         .

        // Suffix 'D' from en_US.aff
        // SFX D Y 4
        // SFX D   0     d          e
        // SFX D   y     ied        [^aeiou]y
        // SFX D   0     ed         [^ey]
        // SFX D   0     ed         [aeiou]y

        // earth/UDYG (en_US.dic line 20997)
        assert!(en_us().check("unearthed"));
    }

    #[test]
    fn check_word_with_double_suffix() {
        // en_US doesn't use continuation flags in prefixes or suffixes so we need to create a
        // small custom dictionary to check this. We'll use part of es_ANY, suffixes 'S' and 'J'
        // trimmed to only the clauses we need.
        let aff = r#"
        SFX J Y 1
        SFX J le ilidad/S ble

        SFX S Y 2
        SFX S 0 s [aceéfgiíkoóptuúw]
        SFX S 0 es [bdhíjlmrúxy]
        "#;

        // es_ANY.dic line 48787
        let dic = r#"1
        perdurable/JS
        "#;

        let dict = Dictionary::new_with_hasher(dic, aff, ahash::RandomState::new()).unwrap();

        // Stem
        assert!(dict.check("perdurable"));
        // Single suffix 'J'
        assert!(dict.check("perdurabilidad"));
        // Single suffix 'S'
        assert!(dict.check("perdurables"));
        // Double suffix. 'S' is the outer suffix then 'J' is the inner suffix.
        assert!(dict.check("perdurabilidades"));
    }
}
