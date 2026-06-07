use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use once_cell::sync::Lazy;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

// French has a much larger affix table than en_US, so checking exercises the affix-stripping
// machinery far more heavily. See <https://github.com/helix-editor/spellbook/issues/15>.
const FR_FR_AFF: &str = include_str!("../vendor/fr_FR/fr.aff");
const FR_FR_DIC: &str = include_str!("../vendor/fr_FR/fr.dic");

type RandomState = foldhash::fast::FixedState;
/// A random seed from a sample run. The values aren't important here: just that they're constant.
/// We don't want the benchmark outputs to reflect random changes to the seed.
const HASHER: RandomState = RandomState::with_seed(16553733157538299820);

static EN_US: Lazy<Dictionary<RandomState>> =
    Lazy::new(|| Dictionary::new_with_hasher(EN_US_AFF, EN_US_DIC, HASHER).unwrap());

static FR_FR: Lazy<Dictionary<RandomState>> =
    Lazy::new(|| Dictionary::new_with_hasher(FR_FR_AFF, FR_FR_DIC, HASHER).unwrap());

fn en_us(c: &mut Criterion) {
    let mut group = c.benchmark_group("check/en_US");

    group.bench_function("in_dictionary_word", |b| {
        b.iter(|| EN_US.check(black_box("earth")))
    });
    group.bench_function("number", |b| {
        b.iter(|| EN_US.check(black_box("8675,309.0")))
    });
    // "earthed" is not a stem in the wordlist - it's "earth" plus the `-ed` suffix - so checking it
    // can only succeed by running the suffix-stripping machinery (`AffixesIter`). (Contrast
    // "earthly", which is a literal stem and short-circuits on the wordlist lookup without
    // exercising suffixes.)
    group.bench_function("word_with_suffix", |b| {
        b.iter(|| EN_US.check(black_box("earthed")))
    });
    group.bench_function("word_with_prefix", |b| {
        b.iter(|| EN_US.check(black_box("unearth")))
    });
    group.bench_function("word_with_prefix_and_suffix", |b| {
        b.iter(|| EN_US.check(black_box("unearthed")))
    });
    group.bench_function("incorrect_prefix", |b| {
        b.iter(|| EN_US.check(black_box("reearth")))
    });
    group.bench_function("uppercase_in_dictionary_word", |b| {
        b.iter(|| EN_US.check(black_box("EARTH")))
    });
    group.bench_function("titlecase_in_dictionary_word", |b| {
        b.iter(|| EN_US.check(black_box("Earth")))
    });
    group.bench_function("breaks", |b| {
        b.iter(|| EN_US.check(black_box("light-weight-like")))
    });
    group.bench_function("compound_word", |b| {
        b.iter(|| EN_US.check(black_box("20000th")))
    });

    group.finish();
}

// French: the large affix table makes these stress the affix-stripping path much harder than their
// en_US equivalents.
fn fr_fr(c: &mut Criterion) {
    let mut group = c.benchmark_group("check/fr_FR");

    group.bench_function("in_dictionary_word", |b| {
        b.iter(|| FR_FR.check(black_box("test")))
    });
    // "mangerais" is not a stem in the wordlist - it's "manger" plus a suffix - so checking it can
    // only succeed by running the suffix-stripping machinery (`AffixesIter`). (Contrast a word like
    // "mangeable" which is a literal stem and short-circuits on the wordlist lookup.)
    group.bench_function("word_with_suffix", |b| {
        b.iter(|| FR_FR.check(black_box("mangerais")))
    });
    // Like `word_with_suffix` but both the input and the stripped suffix contain a multi-byte
    // character ("â"). This stresses the char-by-char decoding inside `AffixesIter`, where indexing
    // the nth character of an affix re-walks the UTF-8 from one end.
    group.bench_function("word_with_suffix_multibyte", |b| {
        b.iter(|| FR_FR.check(black_box("mangeât")))
    });
    group.bench_function("incorrect_word", |b| {
        b.iter(|| FR_FR.check(black_box("foobarbaz")))
    });

    group.finish();
}

criterion_group!(benches, en_us, fr_fr);
criterion_main!(benches);
