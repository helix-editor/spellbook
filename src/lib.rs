use std::ops::Deref;

mod aff;
mod dic;

pub struct Dictionary {
    _dic: dic::Dic,
    _aff: aff::Aff,
    // TODO: personal dictionaries & session changes
}

impl Dictionary {
    // TODO: Result
    pub fn compile(_aff_text: &str, _dic_text: &str) -> Self {
        unimplemented!()
    }

    pub fn check(&self, _word: &str) -> bool {
        unimplemented!()
    }

    pub fn suggest(&self, _word: &str) -> Vec<String> {
        unimplemented!()
    }
}

/// Internal compressed representation of a flag.
pub(crate) type Flag = u32;

/// The set of all flags on a word.
#[derive(Debug, Default, Clone)]
pub(crate) struct FlagSet(Vec<Flag>);

impl From<Vec<Flag>> for FlagSet {
    fn from(mut flags: Vec<Flag>) -> Self {
        flags.sort_unstable();
        flags.dedup();
        FlagSet(flags)
    }
}

impl Deref for FlagSet {
    type Target = Vec<Flag>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Capitalization {
    // Hunspell: "NO"
    Lower,
    // Hunspell: "TITLE"
    Title,
    // Hunspell: "ALL"
    Upper,
    // Hunspell: "HUH"
    Camel,
    // Hunspell: "HUHINIT"
    Pascal,
}
