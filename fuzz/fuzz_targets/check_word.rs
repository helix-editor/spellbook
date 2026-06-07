#![no_main]

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../../vendor/en_US/en_US.dic");

fn dict() -> &'static Dictionary {
    static DICT: OnceLock<Dictionary> = OnceLock::new();
    DICT.get_or_init(|| Dictionary::new(EN_US_AFF, EN_US_DIC).unwrap())
}

// `check` and `suggest` accept arbitrary caller-supplied words. Neither should ever panic on any
// valid UTF-8 input, including unusual Unicode, words at the length boundary, and inputs the
// suggester rewrites in place via its `unsafe` buffer manipulation.
fuzz_target!(|word: &str| {
    let dict = dict();
    let _ = dict.check(word);

    let mut out = Vec::new();
    dict.suggest(word, &mut out);
});
