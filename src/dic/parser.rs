use crate::{
    aff::Aff, FlagSet, MorphologicalFields, ParseDictionaryError, ParseDictionaryErrorKind,
    ParseFlagError,
};

use super::Dic;

pub(crate) fn parse(aff: &Aff, dic_text: &str) -> Result<Dic, ParseDictionaryError> {
    let mut lines = dic_text.lines().enumerate();

    // The first line of the `.dic` has the number of words so we can allocate exactly.
    let entries = match lines.next() {
        Some((line_number, line)) => line
            .parse::<usize>()
            .map_err(|err| error(ParseDictionaryErrorKind::MalformedNumber(err), line_number))?,
        None => return Err(error(ParseDictionaryErrorKind::Empty, 0)),
    };

    let mut dic = Dic::with_capacity(entries);

    for (line_number, line) in lines {
        if line.is_empty() || line.starts_with(|ch: char| ch.is_whitespace()) {
            continue;
        }

        let mut parts = line.split_whitespace();
        let part1 = parts.next().expect("line is non-empty and non-whitespace");
        let (stem, flags) = split_word_and_flags(aff, part1)
            .map_err(|err| error(ParseDictionaryErrorKind::MalformedFlag(err), line_number))?;

        let mut data: MorphologicalFields = Default::default();

        // Current behavior is to drop any that can't be parsed.
        for part in parts {
            match part.split_once(':') {
                Some((key, value)) => {
                    let mut keychars = key.chars();
                    let k1 = match keychars.next() {
                        Some(ch) => ch,
                        None => continue,
                    };
                    let k2 = match keychars.next() {
                        Some(ch) => ch,
                        None => continue,
                    };
                    if value.is_empty() {
                        continue;
                    }

                    data.entry([k1, k2])
                        .or_insert_with(Default::default)
                        .push(value.to_string());
                }
                None => continue,
            };
        }

        let (capitalization, variants) = aff.casing.variants(&stem);
        let word = super::Word {
            stem,
            flags,
            data,
            capitalization,
        };

        dic.insert(word, variants)
    }

    Ok(dic)
}

/// Split a word string and its flags, if any.
/// The input is assumed to be one word without any whitespace or line
/// separators.
pub(crate) fn split_word_and_flags(
    aff: &Aff,
    input: &str,
) -> Result<(String, FlagSet), ParseFlagError> {
    let mut chars = input.chars();
    let mut word = String::new();
    let mut escape = false;
    for ch in chars.by_ref() {
        match ch {
            '\\' => escape = !escape,
            '/' if !escape => break,
            _ => word.push(ch),
        }
    }
    if let Some(ignore_chars) = &aff.ignore_chars {
        word = ignore_chars.erase_ignored(&word)
    }
    let flag_set = aff.flag_type.parse_flags_from_chars(chars)?;

    Ok((word, flag_set))
}

fn error(kind: ParseDictionaryErrorKind, line_number: usize) -> ParseDictionaryError {
    ParseDictionaryError {
        kind,
        source: crate::ParseDictionaryErrorSource::Dic,
        line_number: Some(line_number),
    }
}
