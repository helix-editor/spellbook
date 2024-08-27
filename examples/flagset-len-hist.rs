use hdrhistogram::Histogram;
use std::path::PathBuf;
use std::{
    fs::File,
    io::{self, Read},
    path::Path,
};

use spellbook::Dictionary;

fn main() {
    let mut hist = Histogram::<u64>::new_with_bounds(1, 264, 1).unwrap();

    for dic_path in std::env::args().skip(1) {
        let dic_path = PathBuf::from(dic_path);
        let aff_path = dic_path.with_extension("aff");
        if !aff_path.exists() {
            continue;
        }

        let dic = read_to_string(&dic_path).unwrap();
        let aff = read_to_string(&aff_path).unwrap();
        let name = dic_path.file_stem().unwrap().to_string_lossy();

        let Ok(dict) = Dictionary::new_with_hasher(&dic, &aff, ahash::RandomState::new()) else {
            continue;
        };

        // let max = dict
        //     .aff_data
        //     .words
        //     .iter()
        //     .map(|(_stem, flagset)| flagset.len())
        //     .max()
        //     .unwrap_or_default();
        // println!("dict: '{name}': {max}");

        println!("dict: '{name}'");

        for (_stem, flagset) in dict.aff_data.words.iter() {
            hist.record(flagset.len().try_into().unwrap()).unwrap();
        }
    }

    println!("# of samples: {}", hist.len());
    for v in hist.iter_recorded() {
        println!(
            "{}'th percentile of data is {} with {} samples",
            v.percentile(),
            v.value_iterated_to(),
            v.count_at_value()
        );
    }
}

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
