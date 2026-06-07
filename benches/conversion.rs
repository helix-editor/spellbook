//! Stress benchmark for the ICONV/OCONV conversion table (`ConversionTable::convert`), which runs
//! on every checked word. The interesting axis is the size of the conversion table: `convert` has
//! to decide, for each position in the word, whether any pattern matches there.
//!
//! This builds a dictionary with a large conversion table and checks a word that matches none of
//! the patterns (the common case) so that the whole table is consulted.

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use spellbook::Dictionary;

type RandomState = foldhash::fast::FixedState;
const HASHER: RandomState = RandomState::with_seed(16553733157538299820);

/// Builds a dictionary whose `.aff` has `n` ICONV patterns with diverse first bytes (`a`-`z`) and
/// digits in the body. The benchmark word is made of letters only, so no pattern can match it -
/// every pattern must be ruled out.
fn dict_with_iconv(n: usize) -> Dictionary<RandomState> {
    let mut aff = String::from("SET UTF-8\nICONV ");
    aff.push_str(&n.to_string());
    aff.push('\n');
    for i in 0..n {
        let first = (b'a' + (i % 26) as u8) as char;
        // e.g. "ICONV a0000 a0000x", the digits guarantee it never matches a letters-only word.
        aff.push_str(&format!("ICONV {first}{i:05} {first}{i:05}x\n"));
    }
    let dic = "2\nhello\nworld\n";
    Dictionary::new_with_hasher(&aff, dic, HASHER).unwrap()
}

// A 32-character all-lowercase word: it shares first bytes with the patterns (so the table is
// actually consulted at each position) but matches none of them.
const WORD: &str = "abcdefghijklmnopqrstuvwxyzabcdef";

// A 32-character word whose bytes are all uppercase, so none of them is a pattern start byte
// (`a`-`z`). This exercises the `possible_start_bytes` filter's full scan-and-reject path - the
// overwhelmingly common "nothing to convert" case - rather than `match_at`. This is the case the
// set's representation actually affects, since the whole word is probed against it.
const NO_OVERLAP_WORD: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZABCDEF";

fn conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("conversion");

    for n in [64usize, 1024] {
        let dict = dict_with_iconv(n);
        // The word shares first bytes with the patterns, so the table is consulted at each position.
        group.bench_function(format!("iconv_table_{n}"), |b| {
            b.iter(|| dict.check(black_box(WORD)))
        });
        // The word shares no first byte with any pattern: the `possible_start_bytes` filter rejects.
        group.bench_function(format!("iconv_filter_reject_{n}"), |b| {
            b.iter(|| dict.check(black_box(NO_OVERLAP_WORD)))
        });
    }

    group.finish();
}

criterion_group!(benches, conversion);
criterion_main!(benches);
