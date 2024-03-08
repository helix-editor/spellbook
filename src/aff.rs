use crate::{
    alloc::{
        borrow::Cow,
        string::{String, ToString},
    },
    Flag, FlagSet,
};

use core::marker::PhantomData;

/// The representation of a flag in a `.dic` or `.aff` file.
///
/// This representation also decides how we encode flags into `Flag`. This is controlled by the
/// `FLAG` directive in a `.aff` file.
#[derive(Debug, Clone, Copy)]
pub(crate) enum FlagType {
    /// A single ascii character.
    ///
    /// This is the default representation if a `.aff` file does not specify another.
    Short,
    /// Two adjacent ascii characters.
    ///
    /// The french dictionary uses this. For example for some proper nouns like `Asimov/L'D'Q'`,
    /// `L'` is a flag, `D'` another, `Q'` another.
    Long,
    /// A number in the range `1..=65000`.
    ///
    /// We will approximate this to `2^16`. Numeric flags are separated by commas.
    /// For example `actionfilm/70,7,252,976` from the Danish dictionary.
    Numeric,
    /// One UTF8 character described by at most two bytes.
    Utf8,
}

impl Default for FlagType {
    fn default() -> Self {
        Self::Short
    }
}

#[derive(Debug, Clone)]
pub struct UnknownFlagTypeError(String);

impl core::str::FromStr for FlagType {
    type Err = UnknownFlagTypeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "long" => Ok(Self::Long),
            "num" => Ok(Self::Numeric),
            "UTF-8" => Ok(Self::Utf8),
            _ => Err(UnknownFlagTypeError(s.to_string())),
        }
    }
}

impl core::fmt::Display for UnknownFlagTypeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "expected FLAG to be `long`, `num` or `UTF-8` if set, found {}",
            self.0
        )
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Condition {
    /// The input pattern.
    ///
    /// The condition string is not transformed or compiled into a different input. We'll iterate
    /// over it directly to attempt to match the pattern.
    pattern: String,
    /// The number of `char`s that the pattern describes.
    ///
    /// `Condition` is such a small subset of regex that we can tell only from a linear scan of
    /// the input how many characters we will attempt to match.
    chars: usize,
}

/// An error arising from validating a [`Condition`].
///
/// Conditions are a subset of regular expressions that include positive and negative character
/// classes and the wildcard character. A condition might fail validation if the character classes
/// are open (for example `foo]` or `foo[bar`) or if the condition has an empty character class,
/// which is not valid (`[]`).
// Hands where I can see 'em, clippy. The only time I ever went down was when a machine was easing
// at the wrong time.
#[allow(clippy::enum_variant_names)]
#[derive(Debug, PartialEq, Eq)]
pub enum ConditionError {
    /// The pattern contained an opening `[` character which did not match a closing `]`
    /// character.
    UnopenedCharacterClass,
    /// The pattern contained a closing `]` character which did not match an opening `[`
    /// character.
    UnclosedCharacterClass,
    /// The pattern contained the literal `[]` which is not a valid character class.
    EmptyCharacterClass,
}

impl core::fmt::Display for ConditionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnopenedCharacterClass => {
                f.write_str("closing bracket has no matching opening bracket")
            }
            Self::UnclosedCharacterClass => {
                f.write_str("opening bracket has no matching closing bracket")
            }
            Self::EmptyCharacterClass => f.write_str("empty bracket expression"),
        }
    }
}

impl core::str::FromStr for Condition {
    type Err = ConditionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut scan = s;
        let mut chars = 0;

        // Loop through the characters. We can't just iterate through the `.chars()` because we'll
        // be jumping ahead with the help of `find`.
        loop {
            // Find a bracket. Brackets signal character classes.
            let bracket_index = match scan.find(&['[', ']']) {
                Some(index) => index,
                None => {
                    // If there isn't one, accept the rest of the string.
                    chars += scan.chars().count();
                    break;
                }
            };
            // If there is one, scan ahead to it.
            chars += scan[..bracket_index].chars().count();
            scan = &scan[bracket_index..];
            match scan
                .chars()
                .next()
                .expect("scan can't be empty if the pattern matched")
            {
                ']' => return Err(Self::Err::UnopenedCharacterClass),
                '[' => {
                    scan = &scan[1..];
                    match scan.chars().next() {
                        None => return Err(Self::Err::UnclosedCharacterClass),
                        Some('^') => scan = &scan[1..],
                        _ => (),
                    }

                    match scan.find(']') {
                        None => return Err(Self::Err::UnclosedCharacterClass),
                        Some(0) => return Err(Self::Err::EmptyCharacterClass),
                        Some(bracket_index) => {
                            // Only count the character class as one character.
                            chars += 1;
                            scan = &scan[bracket_index + 1..];
                            continue;
                        }
                    }
                }
                // This is impossible if find `find` found `[` or `]`.
                _ => unreachable!(),
            }
        }

        Ok(Self {
            pattern: String::from(s),
            chars,
        })
    }
}

/// Internal container type for a prefix or suffix.
pub(crate) struct Affix<K> {
    /// The flag that words may use to reference this affix.
    pub flag: Flag,
    /// Whether the affix is compatible with the opposite affix.
    /// For example a word that has both a prefix and a suffix, both the prefix
    /// and suffix should have `crossproduct: true`.
    pub crossproduct: bool,
    /// What is stripped from the stem when the affix is applied.
    pub strip: String,
    /// What should be added when the affix is applied.
    pub add: String,
    /// Condition that the stem should be checked against to query if the
    /// affix is relevant.
    pub condition: Option<Condition>,
    /// Flags the affix has itself.
    pub flags: FlagSet,
    phantom_data: PhantomData<K>,
}
impl<K> Affix<K> {
    pub fn new(
        flag: Flag,
        crossproduct: bool,
        strip: &str,
        add: String,
        condition: Option<&str>,
        flags: FlagSet,
    ) -> Result<Self, ConditionError> {
        let condition = condition.map(str::parse).transpose()?;

        Ok(Self {
            flag,
            crossproduct,
            strip: strip.to_string(),
            add,
            flags,
            condition,
            phantom_data: PhantomData,
        })
    }
}

#[derive(Debug)]
pub(crate) struct Pfx;
#[derive(Debug)]
pub(crate) struct Sfx;

/// Rules for replacing characters at the beginning of a stem.
pub(crate) type Prefix = Affix<Pfx>;
/// Rules for replacing characters at the end of a stem.
pub(crate) type Suffix = Affix<Sfx>;

impl Suffix {
    /// Remove the `add` and add the `strip`
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        if word.ends_with(&self.add) {
            let mut stem = word[..(word.len() - self.add.len())].to_string();
            stem.push_str(&self.strip);
            Cow::Owned(stem)
        } else {
            Cow::Borrowed(word)
        }
    }

    // check_condition
}

impl Prefix {
    /// Remove the `add` and add the `strip`
    pub fn to_stem<'a>(&self, word: &'a str) -> Cow<'a, str> {
        if word.starts_with(&self.add) {
            let mut stem = self.strip.clone();
            stem.push_str(&word[self.add.len()..]);
            Cow::Owned(stem)
        } else {
            Cow::Borrowed(word)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn condition_parse() {
        assert_eq!(
            Err(ConditionError::EmptyCharacterClass),
            "[]".parse::<Condition>()
        );
        assert_eq!(
            Err(ConditionError::UnclosedCharacterClass),
            "[foo".parse::<Condition>()
        );
        assert_eq!(
            Err(ConditionError::UnopenedCharacterClass),
            "foo]".parse::<Condition>()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo".to_string(),
                chars: 3
            }),
            "foo".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo[bar]".to_string(),
                chars: 4
            }),
            "foo[bar]".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "[foo]bar".to_string(),
                chars: 4
            }),
            "[foo]bar".parse()
        );
        assert_eq!(
            Ok(Condition {
                pattern: "foo[bar]baz".to_string(),
                chars: 7
            }),
            "foo[bar]baz".parse()
        );
    }
}
