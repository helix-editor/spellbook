use std::{iter::Peekable, ops::Deref};

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
#[derive(Debug, Default, Clone)]
pub(crate) struct FlagSet(Vec<Flag>);

impl From<Vec<Flag>> for FlagSet {
    fn from(mut flags: Vec<Flag>) -> Self {
        flags.sort_unstable();
        flags.dedup();
        FlagSet(flags)
    }
}

impl From<Option<Flag>> for FlagSet {
    fn from(maybe_flag: Option<Flag>) -> Self {
        Self(match maybe_flag {
            Some(flag) => vec![flag],
            None => vec![],
        })
    }
}

/// A borrowed flag-set slice.
pub(crate) type FlagSetRef<'a> = &'a [Flag];

impl Deref for FlagSet {
    type Target = Vec<Flag>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<[Flag]> for FlagSet {
    fn as_ref(&self) -> FlagSetRef {
        self.as_slice()
    }
}

impl FlagSet {
    // TODO: this will be used by CompoundRule.
    #[allow(dead_code)]
    pub fn intersection<'a>(&'a self, other: FlagSetRef<'a>) -> impl Iterator<Item = Flag> + 'a {
        FlagSetIntersection {
            left: self.iter().copied().peekable(),
            right: other.iter().copied().peekable(),
        }
    }

    // TODO check my math on the next two.

    /// Whether all flags in `other` are members of this flag set.
    pub fn is_superset_of(&self, other: FlagSetRef) -> bool {
        let mut left = self.iter().peekable();
        let mut right = other.iter().peekable();

        loop {
            match (left.peek(), right.peek()) {
                (Some(l), Some(r)) if l == r => {
                    let _ = left.next();
                    let _ = right.next();
                }
                (Some(l), Some(r)) if l < r => {
                    let _ = left.next();
                }
                (Some(l), Some(r)) if l > r => {
                    let _ = right.next();
                }
                (Some(_), Some(_)) => unreachable!(),
                (None, Some(_)) => return false,
                (_, None) => return true,
            }
        }
    }

    /// Whether no flags in `other` are members of this flag set.
    pub fn is_disjoint_of(&self, other: FlagSetRef) -> bool {
        let mut left = self.iter().peekable();
        let mut right = other.iter().peekable();

        loop {
            match (left.peek(), right.peek()) {
                (Some(l), Some(r)) if l == r => return false,
                (Some(l), Some(r)) if l < r => {
                    let _ = left.next();
                }
                (Some(l), Some(r)) if l > r => {
                    let _ = right.next();
                }
                (_, _) => return true,
            }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Capitalization {
    /// Hunspell: "NO"
    Lower,
    /// Hunspell: "INIT"
    Title,
    /// Hunspell: "ALL"
    Upper,
    /// Hunspell: "HUH"
    Camel,
    /// Hunspell: "HUHINIT"
    Pascal,
}
