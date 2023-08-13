use std::collections::{BTreeSet, HashMap};

use aff::ParseCompoundRuleError;
pub use aff::{ParseFlagError, UnknownFlagTypeError};
pub use checker::Checker;

mod aff;
mod checker;
mod dic;
mod stdx;

#[derive(Debug)]
pub struct Dictionary {
    pub(crate) dic: dic::Dic,
    pub(crate) aff: aff::Aff,
    // TODO: personal dictionaries & session changes
}

impl Dictionary {
    pub fn compile(aff_text: &str, dic_text: &str) -> Result<Self, ParseDictionaryError> {
        let aff = aff::parser::parse(aff_text)?;
        let dic = dic::parser::parse(&aff, dic_text)?;

        Ok(Self { aff, dic })
    }

    pub fn check(&self, word: &str) -> bool {
        self.checker().check(word)
    }

    pub fn checker(&self) -> Checker {
        Checker::new(&self.dic, &self.aff)
    }

    pub fn suggest(&self, _word: &str) -> Vec<String> {
        unimplemented!()
    }
}

/// Internal compressed representation of a flag.
pub(crate) type Flag = u32;

/// The set of all flags on a word.
/// Internally this is stored as an ordered set of flags backed
/// by [std::collections::BTreeSet].
pub(crate) type FlagSet = BTreeSet<Flag>;

#[derive(Debug)]
pub struct ParseDictionaryError {
    pub kind: ParseDictionaryErrorKind,
    pub source: ParseDictionaryErrorSource,
    pub line_number: Option<usize>,
}

#[derive(Debug)]
pub enum ParseDictionaryErrorSource {
    Dic,
    Aff,
    // Personal, ?
}

#[derive(Debug)]
pub enum ParseDictionaryErrorKind {
    UnknownFlagType(UnknownFlagTypeError),
    MalformedFlag(ParseFlagError),
    MalformedNumber(std::num::ParseIntError),
    UnexpectedNonWhitespace(char),
    MismatchedArity { expected: usize, actual: usize },
    MismatchedRowCount { expected: usize, actual: usize },
    MalformedCompoundRule(ParseCompoundRuleError),
    MalformedRegex(regex::Error),
    MalformedMorphologicalField(String),
    MalformedAffix,
    Empty,
}

impl From<UnknownFlagTypeError> for ParseDictionaryErrorKind {
    fn from(err: UnknownFlagTypeError) -> Self {
        Self::UnknownFlagType(err)
    }
}

impl From<ParseFlagError> for ParseDictionaryErrorKind {
    fn from(err: ParseFlagError) -> Self {
        Self::MalformedFlag(err)
    }
}

pub(crate) type MorphologicalFields = HashMap<[char; 2], Vec<String>>;

#[cfg(test)]
mod test {
    use crate::{aff::FlagType, FlagSet};

    fn simple_flag_set(flags: &str) -> FlagSet {
        let flag_type = FlagType::Short;
        flag_type
            .parse_flags_from_chars(flags.chars())
            .expect("can parse")
    }

    #[test]
    fn simple_flag_set_invariants() {
        let fs = simple_flag_set("zaZAa");
        assert_eq!(fs, simple_flag_set("AZaz"));
        assert_eq!(fs.len(), 4);
    }

    #[test]
    fn flag_set_algebra() {
        // intersection
        let fs1 = simple_flag_set("abcxyz");
        let fs2 = simple_flag_set("aciwxz");
        let intersection: FlagSet = fs1.intersection(&fs2).cloned().collect();
        assert_eq!(intersection, simple_flag_set("acxz"));

        // superset
        assert!(simple_flag_set("abc").is_superset(&simple_flag_set("b")));
        assert!(simple_flag_set("abc").is_superset(&simple_flag_set("abc")));
        assert!(!simple_flag_set("abc").is_superset(&simple_flag_set("abcd")));
        assert!(!simple_flag_set("ac").is_superset(&simple_flag_set("abc")));
    }
}
