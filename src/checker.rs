//! A container type for checking words.
//! This allows customizing options like whether to allow words
//! that aren't allowed to be suggested.

use std::{borrow::Cow, rc::Rc};

use crate::{
    aff::{Aff, Capitalization, CompoundRule, Prefix, Suffix},
    dic::{Dic, Word},
    stdx::is_some_and,
    FlagSet,
};

/// A hypothesis of how some word might be split into stem, suffix(es)
/// and prefix(es).
#[derive(Debug, Default, Clone)]
pub(crate) struct AffixForm {
    // TODO: rename as "word"?
    text: String,
    pub stem: String,
    prefixes: [Option<Rc<Prefix>>; 2],
    suffixes: [Option<Rc<Suffix>>; 2],
}

impl AffixForm {
    pub(crate) fn has_affixes(&self) -> bool {
        self.prefixes[0].is_some() || self.suffixes[0].is_some()
    }

    pub(crate) fn is_base(&self) -> bool {
        !self.has_affixes()
    }

    pub(crate) fn flags(&self) -> FlagSet {
        let mut flags = FlagSet::new();
        if let Some(prefix) = &self.prefixes[0] {
            flags.extend(prefix.flags.iter());
        }
        if let Some(suffix) = &self.suffixes[0] {
            flags.extend(suffix.flags.iter());
        }
        flags
    }

    pub(crate) fn all_flag_sets(&self) -> impl Iterator<Item = &FlagSet> {
        self.prefixes
            .iter()
            .filter_map(|prefix| prefix.as_ref().map(|pfx| &pfx.flags))
            .chain(
                self.suffixes
                    .iter()
                    .filter_map(|suffix| suffix.as_ref().map(|sfx| &sfx.flags)),
            )
    }
}

/// A hypothesis of how some word could be split into several [AffixForm]s
#[derive(Debug)]
pub(crate) struct CompoundForm {
    pub parts: Vec<AffixForm>,
}

impl CompoundForm {
    pub(crate) fn last(&self) -> &AffixForm {
        self.parts.last().expect("parts should be non-empty")
    }
}

#[derive(Debug, Clone, Copy)]
enum CompoundPosition {
    Begin,
    Middle,
    End,
}

#[derive(Debug)]
pub struct Checker<'a> {
    dic: &'a Dic,
    aff: &'a Aff,
    // TODO personal dictionaries.
    // TODO flip these fields to 'strict_capitalization' and 'forbid_nosuggest'
    /// Whether to allow variances in casing. When `false`, only the
    /// exact casing in the dictionary is considered correct.
    capitalization: bool,
    /// Whether words marked with the `NOSUGGEST` flag should be
    /// considered correct.
    allow_nosuggest: bool,
}

impl<'a> Checker<'a> {
    pub(crate) fn new(dic: &'a Dic, aff: &'a Aff) -> Self {
        Self {
            dic,
            aff,
            capitalization: true,
            allow_nosuggest: true,
        }
    }

    pub fn strict_capitalization(mut self) -> Self {
        self.capitalization = false;
        self
    }

    pub fn forbid_nosuggest(mut self) -> Self {
        self.allow_nosuggest = false;
        self
    }

    /// Check whether a word is considered correct by the dictionary.
    pub fn check(&self, word: &str) -> bool {
        if is_some_and(self.aff.forbidden_word_flag, |flag| {
            self.dic.has_flag(word, flag, true)
        }) {
            return false;
        }

        let word = match &self.aff.input_conversion {
            Some(iconv) => iconv.apply(word),
            None => Cow::Borrowed(word),
        };

        let word = match &self.aff.ignore_chars {
            Some(ignore) => ignore.erase_ignored(word.as_ref()),
            None => word.to_string(),
        };

        // Always accept numbers.
        if word.chars().all(|ch| ch.is_numeric()) {
            return true;
        }

        self.check_word_break_permutations(&word)
    }

    /// Permute the possible breaks and check if any interpretation is correct.
    ///
    /// For example if "pre-processed-meat" is being checked, check:
    ///
    /// * `["pre-processed-meat"]`
    /// * `["pre", "processed-meat"]`
    /// * `["pre-processed", "meat"]`
    /// * `["pre", "processed", "meat"]`
    ///
    /// Returns `true` if there exists any permutation of which all words are
    /// correct.
    fn check_word_break_permutations(&self, word: &str) -> bool {
        self.check_word_break_permutations_impl(word, 0, 0)
    }

    fn check_word_break_permutations_impl(&self, word: &str, cursor: usize, depth: usize) -> bool {
        let is_correct_word = |part| self.has_any_form(part, true, true);

        if is_correct_word(word) {
            return true;
        }

        if depth > 10 {
            return false;
        }

        for pattern in &self.aff.break_patterns {
            let idx = match pattern.find(&word[cursor..]) {
                Some(idx) => idx,
                None => continue,
            };
            let start = &word[..cursor + idx];
            let rest = &word[idx + pattern.len()..];

            if (is_correct_word(start)
                && self.check_word_break_permutations_impl(rest, 0, depth + 1))
                || self.check_word_break_permutations_impl(word, cursor + idx, depth + 1)
            {
                return true;
            }
        }

        false
    }

    /// Checks if a given word has a correct form in the dictionary.
    fn has_any_form(
        &self,
        word: &str,
        include_affix_forms: bool,
        include_compound_forms: bool,
    ) -> bool {
        let (captype, variants) = if self.capitalization {
            self.aff.casing.variants(word)
        } else {
            let captype = self.aff.casing.guess(word);
            (captype, vec![word.to_string()])
        };

        for variant in variants {
            if include_affix_forms {
                for form in self.affix_forms(
                    &variant,
                    captype,
                    &Default::default(),
                    &Default::default(),
                    &Default::default(),
                    None,
                    false,
                ) {
                    if !(self.aff.check_sharps
                        && form.stem.contains('ß')
                        && is_some_and(self.aff.keep_case_flag, |flag| {
                            form.flags().contains(&flag)
                        }))
                    {
                        return true;
                    }
                }
            }

            if include_compound_forms && !self.compound_forms(&variant, captype).is_empty() {
                return true;
            }
        }

        false
    }

    #[allow(clippy::too_many_arguments)]
    fn affix_forms(
        &self,
        word: &str,
        capitalization: Capitalization,
        prefix_flags: &FlagSet,
        suffix_flags: &FlagSet,
        forbidden_flags: &FlagSet,
        compound_pos: Option<CompoundPosition>,
        with_forbidden: bool,
    ) -> Vec<AffixForm> {
        let mut forms = Vec::new();

        for form in self.produce_affix_forms(
            word,
            prefix_flags,
            suffix_flags,
            forbidden_flags,
            compound_pos,
        ) {
            let mut found = false;
            let mut homonyms = self.dic.homonyms(&form.stem, false);

            if !with_forbidden
                && (compound_pos.is_some() || form.has_affixes())
                && is_some_and(self.aff.forbidden_word_flag, |flag| {
                    homonyms.any(|homonym| homonym.flags.contains(&flag))
                })
            {
                // TODO: this is a 'return' in spylls but shouldn't it be a 'continue'?
                return forms;
            }

            for homonym in homonyms {
                if self.is_good_form(&form, homonym, compound_pos, capitalization) {
                    found = true;
                    forms.push(form.clone());
                }
            }

            if matches!(compound_pos, Some(CompoundPosition::Begin))
                && self.aff.force_uppercase_flag.is_some()
                && matches!(capitalization, Capitalization::Title)
            {
                for homonym in self.dic.homonyms(&form.stem.to_lowercase(), false) {
                    if self.is_good_form(&form, homonym, compound_pos, capitalization) {
                        found = true;
                        forms.push(form.clone());
                    }
                }
            }

            if found || compound_pos.is_some() || !matches!(capitalization, Capitalization::Upper) {
                continue;
            }

            if matches!(self.aff.casing.guess(word), Capitalization::Lower) {
                for homonym in self.dic.homonyms(&form.stem, false) {
                    if self.is_good_form(&form, homonym, compound_pos, capitalization) {
                        forms.push(form.clone());
                    }
                }
            }
        }

        forms
    }

    fn produce_affix_forms(
        &self,
        word: &str,
        // TODO: are these two optional?
        prefix_flags: &FlagSet,
        suffix_flags: &FlagSet,
        forbidden_flags: &FlagSet,
        compound_pos: Option<CompoundPosition>,
    ) -> Vec<AffixForm> {
        let mut forms = Vec::new();

        forms.push(AffixForm {
            text: word.to_string(),
            stem: word.to_string(),
            ..Default::default()
        });

        let suffix_allowed =
            matches!(compound_pos, None | Some(CompoundPosition::End)) || !suffix_flags.is_empty();
        let prefix_allowed = matches!(compound_pos, None | Some(CompoundPosition::Begin))
            || !prefix_flags.is_empty();

        if suffix_allowed {
            forms.append(&mut self.desuffix(word, suffix_flags, forbidden_flags, false, false));
        }

        if prefix_allowed {
            for form in self.deprefix(word, prefix_flags, forbidden_flags, false, false) {
                forms.push(form.clone());
                if suffix_allowed
                    && is_some_and(form.prefixes[0].as_ref(), |prefix| prefix.crossproduct)
                {
                    for form2 in
                        self.desuffix(&form.stem, suffix_flags, forbidden_flags, false, true)
                    {
                        forms.push(AffixForm {
                            text: form.text.clone(),
                            prefixes: form.prefixes.clone(),
                            ..form2
                        });
                    }
                }
            }
        }

        forms
    }

    fn desuffix(
        &self,
        word: &str,
        required_flags: &FlagSet,
        forbidden_flags: &FlagSet,
        nested: bool,
        crossproduct: bool,
    ) -> Vec<AffixForm> {
        let mut forms = Vec::new();
        let is_valid_suffix = |suffix: &Rc<Suffix>| {
            (!crossproduct || suffix.crossproduct)
                && suffix.flags.is_superset(required_flags)
                && suffix.flags.is_disjoint(forbidden_flags)
        };

        for suffix in self.aff.suffixes_index.get(word.chars().rev()) {
            if !is_valid_suffix(suffix) {
                continue;
            }

            let stem = suffix.to_stem(word);
            if is_some_and(suffix.condition_pattern.as_ref(), |pattern| {
                !pattern.matches_at_end(&stem)
            }) {
                continue;
            }

            // TODO: builder
            forms.push(AffixForm {
                text: word.to_string(),
                stem: stem.to_string(),
                suffixes: [Some(suffix.clone()), None],
                prefixes: [None, None],
            });

            if !nested {
                let mut required_flags = required_flags.clone();
                required_flags.insert(suffix.flag);
                forms.append(&mut self.desuffix(
                    &stem,
                    &required_flags,
                    forbidden_flags,
                    true,
                    crossproduct,
                ));
            }
        }

        forms
    }

    fn deprefix(
        &self,
        word: &str,
        required_flags: &FlagSet,
        forbidden_flags: &FlagSet,
        nested: bool,
        crossproduct: bool,
    ) -> Vec<AffixForm> {
        let mut forms = Vec::new();
        let is_valid_prefix = |prefix: &Rc<Prefix>| {
            (!crossproduct || prefix.crossproduct)
                && prefix.flags.is_superset(required_flags)
                && prefix.flags.is_disjoint(forbidden_flags)
        };

        for prefix in self.aff.prefixes_index.get(word.chars()) {
            if !is_valid_prefix(prefix) {
                continue;
            }

            let stem = prefix.to_stem(word);
            if is_some_and(prefix.condition_pattern.as_ref(), |pattern| {
                !pattern.matches_at_start(&stem)
            }) {
                continue;
            }

            // TODO: builder
            forms.push(AffixForm {
                text: word.to_string(),
                stem: stem.to_string(),
                prefixes: [Some(prefix.clone()), None],
                suffixes: [None, None],
            });

            if !nested && self.aff.complex_prefixes {
                let mut required_flags = required_flags.clone();
                required_flags.insert(prefix.flag);
                forms.append(&mut self.deprefix(
                    &stem,
                    &required_flags,
                    forbidden_flags,
                    true,
                    crossproduct,
                ));
            }
        }

        forms
    }

    /// Check if an affix form is valid for the given compound position and
    /// capitalization and other rules from the `.aff` file.
    fn is_good_form(
        &self,
        form: &AffixForm,
        word: &Word,
        compound_pos: Option<CompoundPosition>,
        capitalization: Capitalization,
    ) -> bool {
        use crate::stdx::is_none_or;

        let root_flags = &word.flags;
        let all_flags = {
            let mut flags = form.flags();
            flags.extend(word.flags.iter());
            flags
        };

        if !self.allow_nosuggest
            && is_some_and(self.aff.no_suggest_flag, |flag| root_flags.contains(&flag))
        {
            return false;
        }

        if capitalization != word.capitalization
            && is_some_and(self.aff.keep_case_flag, |flag| root_flags.contains(&flag))
            && !(self.aff.check_sharps && word.stem.contains('ß'))
        {
            return false;
        }

        if let Some(flag) = self.aff.need_affix_flag {
            if root_flags.contains(&flag) && !form.has_affixes() {
                return false;
            }

            if form.has_affixes() && form.all_flag_sets().all(|flags| flags.contains(&flag)) {
                return false;
            }
        }

        if is_some_and(form.prefixes[0].as_ref(), |prefix| {
            !all_flags.contains(&prefix.flag)
        }) {
            return false;
        }
        if is_some_and(form.suffixes[0].as_ref(), |suffix| {
            !all_flags.contains(&suffix.flag)
        }) {
            return false;
        }

        if let Some(flag) = self.aff.circumfix_flag {
            let has_suffix = is_some_and(form.suffixes[0].as_ref(), |suffix| {
                suffix.flags.contains(&flag)
            });
            let has_prefix = is_some_and(form.prefixes[0].as_ref(), |prefix| {
                prefix.flags.contains(&flag)
            });
            if has_suffix != has_prefix {
                return false;
            }
        }

        match compound_pos {
            Some(pos) => {
                if is_some_and(self.aff.compound_flag, |flag| all_flags.contains(&flag)) {
                    return true;
                }

                let flag = match pos {
                    CompoundPosition::Begin => self.aff.compound_begin_flag,
                    CompoundPosition::Middle => self.aff.compound_middle_flag,
                    CompoundPosition::End => self.aff.compound_end_flag,
                };

                is_some_and(flag, |flag| all_flags.contains(&flag))
            }
            None => is_none_or(self.aff.only_in_compound_flag, |flag| {
                !all_flags.contains(&flag)
            }),
        }
    }

    fn compound_forms(&self, word: &str, capitalization: Capitalization) -> Vec<CompoundForm> {
        if let Some(flag) = self.aff.forbidden_word_flag {
            for form in self.affix_forms(
                word,
                capitalization,
                &Default::default(),
                &Default::default(),
                &Default::default(),
                None,
                true,
            ) {
                if form.flags().contains(&flag) {
                    return vec![];
                }
            }
        }

        let mut forms = Vec::new();
        if self.aff.compound_begin_flag.is_some() || self.aff.compound_flag.is_some() {
            for compound in self.compounds_by_flags(word, capitalization) {
                if !self.is_bad_compound(&compound, capitalization) {
                    forms.push(compound);
                }
            }
        }

        if !self.aff.compound_rules.is_empty() {
            for compound in self.compounds_by_rules(word) {
                if !self.is_bad_compound(&compound, capitalization) {
                    forms.push(compound);
                }
            }
        }

        forms
    }

    fn compounds_by_flags(&self, word: &str, capitalization: Capitalization) -> Vec<CompoundForm> {
        let mut permit_flags = FlagSet::new();
        if let Some(flag) = self.aff.compound_permit_flag {
            permit_flags.insert(flag);
        }
        let mut forbidden_flags = FlagSet::new();
        if let Some(flag) = self.aff.compound_forbid_flag {
            forbidden_flags.insert(flag);
        }
        self.compounds_by_flags_impl(word, capitalization, &permit_flags, &forbidden_flags, 0)
    }

    fn compounds_by_flags_impl(
        &self,
        word: &str,
        capitalization: Capitalization,
        permit_flags: &FlagSet,
        forbidden_flags: &FlagSet,
        depth: usize,
    ) -> Vec<CompoundForm> {
        // TODO: unroll recursion.
        let mut forms = Vec::new();

        if depth > 0 {
            for form in self.affix_forms(
                word,
                capitalization,
                permit_flags,
                &Default::default(),
                forbidden_flags,
                Some(CompoundPosition::End),
                false,
            ) {
                forms.push(CompoundForm { parts: vec![form] });
            }
        }

        let word_len = word.chars().count();
        if word_len < self.aff.compound_min_length * 2
            || is_some_and(self.aff.max_compound_word_count, |count| count >= depth)
        {
            return forms;
        }

        let default_permit_flags = &Default::default();
        let (compound_pos, prefix_flags) = if depth == 0 {
            (CompoundPosition::Begin, default_permit_flags)
        } else {
            (CompoundPosition::Middle, permit_flags)
        };

        for split_pos in self.aff.compound_min_length..(word_len - self.aff.compound_min_length + 1)
        {
            let splitword: String = word.chars().take(split_pos).collect();
            let rest: String = word.chars().skip(split_pos).collect();

            for form in self.affix_forms(
                &splitword,
                capitalization,
                prefix_flags,
                permit_flags,
                forbidden_flags,
                Some(compound_pos),
                false,
            ) {
                for mut partial in self.compounds_by_flags_impl(
                    &rest,
                    capitalization,
                    permit_flags,
                    forbidden_flags,
                    depth + 1,
                ) {
                    let mut parts = vec![form.clone()];
                    parts.append(&mut partial.parts);
                    forms.push(CompoundForm { parts });
                }
            }

            // handle SIMPLIFIEDTRIPLE
            if self.aff.simplified_triple {
                let ch = splitword.chars().last().expect("split word is non-empty");
                if rest.chars().next().expect("rest word is non-empty") == ch {
                    let mut with_triple = splitword.clone();
                    with_triple.push(ch);
                    for form in self.affix_forms(
                        &with_triple,
                        capitalization,
                        prefix_flags,
                        permit_flags,
                        forbidden_flags,
                        Some(compound_pos),
                        false,
                    ) {
                        for mut partial in self.compounds_by_flags_impl(
                            &rest,
                            capitalization,
                            permit_flags,
                            forbidden_flags,
                            depth + 1,
                        ) {
                            let mut form = form.clone();
                            form.text = with_triple.clone();
                            let mut parts = vec![form];
                            parts.append(&mut partial.parts);
                            forms.push(CompoundForm { parts });
                        }
                    }
                }
            }
        }

        forms
    }

    fn compounds_by_rules(&self, word: &str) -> Vec<CompoundForm> {
        self.compounds_by_rules_impl(word, Vec::new(), &self.aff.compound_rules)
    }

    fn compounds_by_rules_impl(
        &self,
        word: &str,
        prev_parts: Vec<&'a Word>,
        rules: &[CompoundRule],
    ) -> Vec<CompoundForm> {
        let mut forms = Vec::new();

        if !prev_parts.is_empty() {
            for homonym in self.dic.homonyms(word, false) {
                let flag_sets: Vec<&FlagSet> = prev_parts
                    .iter()
                    .map(|part| &part.flags)
                    .chain(std::iter::once(&homonym.flags))
                    .collect();
                if rules.iter().any(|rule| rule.full_match(&flag_sets)) {
                    let form = AffixForm {
                        text: word.to_string(),
                        stem: word.to_string(),
                        ..Default::default()
                    };
                    forms.push(CompoundForm { parts: vec![form] });
                }
            }
        }

        let word_len = word.chars().count();
        if word_len < self.aff.compound_min_length * 2
            || is_some_and(self.aff.max_compound_word_count, |count| {
                prev_parts.len() >= count
            })
        {
            return forms;
        }

        for split_pos in self.aff.compound_min_length..(word_len - self.aff.compound_min_length + 1)
        {
            let splitword: String = word.chars().take(split_pos).collect();

            for homonym in self.dic.homonyms(&splitword, false) {
                let flag_sets: Vec<&FlagSet> = prev_parts
                    .iter()
                    .map(|part| &part.flags)
                    .chain(std::iter::once(&homonym.flags))
                    .collect();
                let compound_rules: Vec<_> = rules
                    .iter()
                    .filter(|rule| rule.partial_match(&flag_sets))
                    // TODO: don't clone.
                    .cloned()
                    .collect();
                if !compound_rules.is_empty() {
                    let rest: String = word.chars().skip(split_pos).collect();
                    let mut parts = prev_parts.clone();
                    parts.push(homonym);
                    for mut rest in self.compounds_by_rules_impl(&rest, parts, &compound_rules) {
                        let form = AffixForm {
                            text: splitword.to_string(),
                            stem: splitword.to_string(),
                            ..Default::default()
                        };
                        let mut parts = vec![form];
                        parts.append(&mut rest.parts);
                        forms.push(CompoundForm { parts });
                    }
                }
            }
        }

        forms
    }

    /// Check if a compound is allowed by the compounding rules in the `.aff`.
    fn is_bad_compound(&self, compound: &CompoundForm, capitalization: Capitalization) -> bool {
        if is_some_and(self.aff.force_uppercase_flag, |flag| {
            !matches!(
                capitalization,
                Capitalization::Upper | Capitalization::Title
            ) && self.dic.has_flag(&compound.last().stem, flag, false)
        }) {
            return true;
        }

        for (i, left_hypothesis) in compound.parts.iter().enumerate() {
            if i == compound.parts.len() - 1 {
                break;
            };

            let left = &left_hypothesis.text;
            let right_hypothesis = &compound.parts[i + 1];
            let right = &right_hypothesis.text;

            if is_some_and(self.aff.compound_forbid_flag, |flag| {
                self.dic.has_flag(left, flag, false)
            }) {
                return true;
            }

            if !self
                .affix_forms(
                    &format!("{left} {right}"),
                    capitalization,
                    &Default::default(),
                    &Default::default(),
                    &Default::default(),
                    None,
                    false,
                )
                .is_empty()
            {
                return true;
            }

            if self.aff.check_compound_replacement {
                unimplemented!("see CHECKCOMPOUNDREP part of is_bad_compount");
            }

            if self.aff.check_compound_triple {
                use crate::stdx::iter_is_one_value;
                // Prohibit triple letters on the bounds of the words.
                // For example "foobb" plus "bar".
                let has_triplicate =
                    iter_is_one_value(left.chars().rev().take(2).chain(right.chars().take(1)))
                        || iter_is_one_value(
                            left.chars().rev().take(1).chain(right.chars().take(2)),
                        );
                if has_triplicate {
                    return true;
                }
            }

            if self.aff.check_compound_case {
                // Prohibit capitalized letters on the bounds of compound parts.
                let rc = right
                    .chars()
                    .next()
                    .expect("compound words should be non-empty");
                let lc = left
                    .chars()
                    .last()
                    .expect("compound words should be non-empty");

                if (rc.is_uppercase() || lc.is_uppercase()) && rc != '-' && lc != '-' {
                    return true;
                }
            }

            if !self.aff.check_compound_pattern.is_empty()
                && self
                    .aff
                    .check_compound_pattern
                    .iter()
                    .any(|pattern| pattern.r#match(left_hypothesis, right_hypothesis))
            {
                // CHECKCOMPPOUNDPATTERN has special rules for disallowing compounds
                // that are otherwise valid constructions.
                return true;
            }

            if self.aff.check_compound_dupe && left == right && i == compound.parts.len() - 2 {
                // Duplication seems to only be disallowed at the end of words.
                return true;
            }
        }

        false
    }
}
