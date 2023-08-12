use std::collections::BTreeSet;

pub use checker::Checker;

mod aff;
mod checker;
mod dic;
mod stdx;

pub struct Dictionary {
    pub(crate) dic: dic::Dic,
    pub(crate) aff: aff::Aff,
    // TODO: personal dictionaries & session changes
}

impl Dictionary {
    // TODO: Result
    pub fn compile(_aff_text: &str, _dic_text: &str) -> Self {
        unimplemented!()
    }

    pub fn check(&self, word: &str) -> bool {
        Checker::new(&self.dic, &self.aff).check(word)
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
