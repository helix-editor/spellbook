#![no_main]

use libfuzzer_sys::fuzz_target;

// `Dictionary::new` parses untrusted `.aff` and `.dic` files, so it must only ever return `Ok` or
// `Err`: it should never panic, no matter how malformed the input is.
//
// The fuzzer feeds a single blob. We split it on the first NUL byte so it can explore both files
// independently (the `.aff` half before the NUL, the `.dic` half after it). Dictionary files are
// text, so we only proceed on valid UTF-8 input.
fuzz_target!(|data: &[u8]| {
    let Ok(text) = core::str::from_utf8(data) else {
        return;
    };

    let (aff, dic) = match text.split_once('\0') {
        Some((aff, dic)) => (aff, dic),
        None => (text, ""),
    };

    let _ = spellbook::Dictionary::new(aff, dic);
});
