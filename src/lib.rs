use std::{iter::Peekable, ops::Deref};

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

impl FlagSet {
    pub fn intersection<'a>(&'a self, other: &'a FlagSet) -> impl Iterator<Item = Flag> + 'a {
        FlagSetIntersection {
            left: self.iter().copied().peekable(),
            right: other.iter().copied().peekable(),
        }
    }
}

/// Since flag sets are ordered and deduplicated, we can find the intersection
/// of two flag sets N and M in `O(|N| + |M|)` time by zipping through both.
pub(crate) struct FlagSetIntersection<L: Iterator<Item = Flag>, R: Iterator<Item = Flag>> {
    left: Peekable<L>,
    right: Peekable<R>,
}

impl<L, R> Iterator for FlagSetIntersection<L, R>
where
    L: Iterator<Item = Flag>,
    R: Iterator<Item = Flag>,
{
    type Item = Flag;

    fn next(&mut self) -> Option<Self::Item> {
        use std::cmp::Ordering::*;

        loop {
            let left = self.left.peek()?;
            let right = self.right.peek()?;

            match left.cmp(right) {
                Equal => {
                    let _ = self.left.next();
                    return self.right.next();
                }
                Less => {
                    let _ = self.left.next();
                }
                Greater => {
                    let _ = self.right.next();
                }
            }
        }
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
