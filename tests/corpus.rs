use spellbook::Dictionary;
use std::{
    fs::{self, File},
    io::{self, Read},
    path::Path,
};

#[test]
fn check() {
    let needs_fixing: hashbrown::HashSet<&str, std::hash::BuildHasherDefault<ahash::AHasher>> = [
        // Use CHECKCOMPOUNDPATTERN replacements which aren't implemented yet.
        "checkcompoundpattern2",
        "checkcompoundpattern3",
        "checkcompoundpattern4",
        // TODO figure out why these fail.
        "condition",
        "encoding",
        "germancompounding",
        "germancompoundingold",
        "hu",
        "i54980",
        "iconv2",
        "ignore",
        "ignoreutf",
        "morph",
        "nepali",
        "oconv",
        "onlyincompound",
        "slash",
        "utf8_bom",
        "utf8_bom2",
        "utf8_nonbmp",
    ]
    .into_iter()
    .collect();

    for file in glob::glob("./tests/corpus/*.dic").unwrap() {
        let file = file.unwrap();
        let path = file.as_path();
        if !path.extension().is_some_and(|ext| ext == "dic") {
            continue;
        }
        let case = path.file_stem().unwrap().to_string_lossy();
        eprintln!("-- case {case:?} --");
        if needs_fixing.contains(case.as_ref()) {
            eprintln!("skipped case {case:?}");
            continue;
        }

        let dic = read_to_string(path).unwrap();
        let aff = read_to_string(path.with_extension("aff")).unwrap();

        let dict = Dictionary::new(&dic, &aff).unwrap();

        for good_word in fs::read_to_string(path.with_extension("good"))
            .iter()
            .flat_map(|text| text.lines())
        {
            assert!(
                dict.check(good_word),
                "case {case:?}: expected {good_word:?} to be correct but it was incorrect"
            );
        }

        for wrong_word in fs::read_to_string(path.with_extension("wrong"))
            .iter()
            .flat_map(|text| text.lines())
        {
            assert!(
                !dict.check(wrong_word),
                "case {case:?}: expected {wrong_word:?} to be incorrect but it was correct"
            );
        }

        println!("case {case:?} passed");
    }
}

// Once the suggest API is in place we can add a `suggest` case which looks for the glob
// `tests/corpus/*.sug` and tries to suggest words for every line in `case.wrong`.

/// Reads the contents of a file into a String, handling detecting and decoding of non-UTF-8
/// contents.
fn read_to_string<P: AsRef<Path>>(path: P) -> io::Result<String> {
    // Adapted from Helix's document opening function:
    // <https://github.com/helix-editor/helix/blob/620dfceb849d6b68d41d4f7678bb4675009fef4d/helix-view/src/document.rs#L395>

    const BUF_SIZE: usize = 8 * 1024;
    let mut buf = [0u8; BUF_SIZE];
    let mut reader = File::open(path).unwrap();
    let read = reader.read(&mut buf).unwrap();
    assert_ne!(read, 0);

    // Guess encoding.
    let mut detector = chardetng::EncodingDetector::new();
    detector.feed(&buf, read < BUF_SIZE);
    let encoding = detector.guess(None, true);

    let mut decoder = encoding.new_decoder();
    let mut output = String::new();
    let mut slice = &buf[..read];
    let mut is_empty = read == 0;
    let mut total_written = 0usize;
    // Zero-initialized bytes are a valid str.
    let mut buf_out = [0u8; BUF_SIZE];
    let buf_str = unsafe { std::str::from_utf8_unchecked_mut(&mut buf_out) };
    loop {
        let mut total_read = 0usize;

        // An inner loop is necessary as it is possible that the input buffer
        // may not be completely decoded on the first `decode_to_str()` call
        // which would happen in cases where the output buffer is filled to
        // capacity.
        loop {
            let (result, read, written, ..) = decoder.decode_to_str(
                &slice[total_read..],
                &mut buf_str[total_written..],
                is_empty,
            );

            // These variables act as the read and write cursors of `buf` and `buf_str` respectively.
            // They are necessary in case the output buffer fills before decoding of the entire input
            // loop is complete. Otherwise, the loop would endlessly iterate over the same `buf` and
            // the data inside the output buffer would be overwritten.
            total_read += read;
            total_written += written;
            match result {
                encoding_rs::CoderResult::InputEmpty => {
                    assert_eq!(slice.len(), total_read);
                    break;
                }
                encoding_rs::CoderResult::OutputFull => {
                    assert!(slice.len() > total_read);
                    output.push_str(&buf_str[..total_written]);
                    total_written = 0;
                }
            }
        }
        // Once the end of the stream is reached, the output buffer is
        // flushed and the loop terminates.
        if is_empty {
            assert_eq!(reader.read(&mut buf)?, 0);
            output.push_str(&buf_str[..total_written]);
            break;
        }

        // Once the previous input has been processed and decoded, the next set of
        // data is fetched from the reader. The end of the reader is determined to
        // be when exactly `0` bytes were read from the reader, as per the invariants
        // of the `Read` trait.
        let read = reader.read(&mut buf)?;
        slice = &buf[..read];
        is_empty = read == 0;
    }

    Ok(output)
}
