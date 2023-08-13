//! Contents of a dictionary.
//! This comes from Hunspell `.dic` files.

// TODO: remove this once parsing and suggestion are done.
#![allow(dead_code)]

pub(crate) mod parser;

use std::collections::HashMap;

use crate::{aff::Capitalization, Flag, FlagSet};

#[derive(Debug, Clone)]
pub(crate) struct Word {
    // can we cut down on string storage? intern strings?
    pub stem: String,
    pub flags: FlagSet,
    pub data: HashMap<[char; 2], Vec<String>>,
    pub capitalization: Capitalization,
}

impl Word {
    pub fn alternate_spellings(&self) -> &[String] {
        self.data
            .get(&['p', 'h'])
            .map(|alts| alts.as_slice())
            .unwrap_or_default()
    }
}

#[derive(Default, Clone)]
pub(crate) struct Dic {
    pub words: Vec<Word>,
    pub index: HashMap<String, Vec<usize>>,
    pub lowercase_index: HashMap<String, Vec<usize>>,
}

impl std::fmt::Debug for Dic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Dic")
            .field("words", &format!("{} entries", self.words.len()))
            .finish_non_exhaustive()
    }
}

impl Dic {
    /// Create a new Dic with the given `capacity`.
    ///
    /// `.dic` files start with a line that gives the exact capacity
    /// of the wordlist.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            words: Vec::with_capacity(capacity),
            index: HashMap::with_capacity(capacity),
            lowercase_index: HashMap::default(),
        }
    }

    /// Return all `Word` instances with the same stem,
    /// optionally ignoring the casing of the words.
    pub(crate) fn homonyms(&self, stem: &str, ignore_case: bool) -> impl Iterator<Item = &Word> {
        use crate::stdx::EitherIterator::{Left, Right};

        let index = if ignore_case {
            &self.lowercase_index
        } else {
            &self.index
        };

        if !index.contains_key(stem) {
            return Left(std::iter::empty());
        }

        Right(index[stem].iter().map(|idx| &self.words[*idx]))
    }

    /// Query if any or all of the homonyms of the stem contain the given flag.
    pub(crate) fn has_flag(&self, stem: &str, flag: Flag, for_all: bool) -> bool {
        let mut homonyms = self.homonyms(stem, false);
        let has_flag = |homonym: &Word| homonym.flags.contains(&flag);

        if for_all {
            homonyms.all(has_flag)
        } else {
            homonyms.any(has_flag)
        }
    }

    /// Inserts the word into the dictionary and links any lowercase variants.
    pub(crate) fn insert(&mut self, word: Word, lowercase_variants: Vec<String>) {
        let index = self.words.len();
        let stem = word.stem.clone(); // TODO interning could turn this into a Copy
        self.words.push(word);
        self.index.entry(stem).or_insert_with(Vec::new).push(index);
        for variant in lowercase_variants {
            self.lowercase_index
                .entry(variant)
                .or_insert_with(Vec::new)
                .push(index);
        }
    }
}
