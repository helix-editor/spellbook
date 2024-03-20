use core::hash::BuildHasher;

use crate::aff::AffData;

// TODO: check what this is in Hunspell. Add docs.
const MAX_WORD_LEN: usize = 360;

/// Checks that the word is valid according to the dictionary.
pub(crate) fn check<S: BuildHasher>(_aff_data: &AffData<S>, word: &str) -> bool {
    if word.len() > MAX_WORD_LEN {
        return false;
    }

    // TODO: iconv

    if word.is_empty() {
        return true;
    }

    // TODO: abbreviation

    if is_number(word) {
        return true;
    }

    // TODO: erase chars

    // TODO: break patterns

    // TODO: abbreviation + break patterns

    todo!()
}

/// Checks if the input word is a number.
///
/// Numbers may have a leading `-` and can have separators within the number of `,`, `.` or `-`,
/// but not more than one separating digits.
fn is_number(word: &str) -> bool {
    let input = word.strip_prefix('-').unwrap_or(word);

    let mut separated = true;
    for ch in input.chars() {
        match ch {
            '0'..='9' => separated = false,
            '.' | '-' | ',' if !separated => separated = true,
            _ => return false,
        }
    }

    true
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn is_number_test() {
        assert!(is_number("123"));
        assert!(is_number("-123"));
        assert!(!is_number("--123"));
        assert!(!is_number(".123"));
        assert!(is_number("0.123"));
        assert!(is_number("8675-309"));
    }
}
