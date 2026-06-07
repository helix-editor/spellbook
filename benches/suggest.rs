use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use once_cell::sync::Lazy;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

// The French dictionary has a much larger affix table than en_US (thousands of suffix rules
// versus dozens). Suggestion is dominated by checking generated candidate words against that
// table, so French exercises the affix-stripping hot paths that en_US barely touches. See
// <https://github.com/helix-editor/spellbook/issues/15>.
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

/// Runs `suggest` repeatedly, reusing the output `Vec` across iterations as a real caller would.
fn bench_suggest(b: &mut criterion::Bencher, dict: &Dictionary<RandomState>, word: &str) {
    let mut out = Vec::new();
    b.iter(|| {
        dict.suggest(black_box(word), &mut out);
        black_box(out.len())
    });
}

// en_US: with so few affixes, suggestion time here is dominated by ngram similarity and the
// cheaper edit-based methods rather than affix stripping.
fn en_us(c: &mut Criterion) {
    let mut group = c.benchmark_group("suggest/en_US");

    // "ansi" -> "ANSI": a quick uppercase suggestion.
    group.bench_function("uppercase", |b| bench_suggest(b, &EN_US, "ansi"));
    // A transposition that edit-based methods can correct ("example").
    group.bench_function("edit", |b| bench_suggest(b, &EN_US, "exmaple"));
    // A misspelling with no cheap edit hit, forcing the ngram pass over the word list.
    group.bench_function("ngram", |b| bench_suggest(b, &EN_US, "impecable"));

    group.finish();
}

// fr_FR: the affix-heavy path from issue #15.
fn fr_fr(c: &mut Criterion) {
    let mut group = c.benchmark_group("suggest/fr_FR");

    group.bench_function("correct_word", |b| bench_suggest(b, &FR_FR, "test"));
    group.bench_function("impecable", |b| bench_suggest(b, &FR_FR, "impécable"));
    group.bench_function("receptioniste", |b| {
        bench_suggest(b, &FR_FR, "réceptioniste")
    });
    // No good suggestion exists, so every suggestion strategy runs to completion.
    group.bench_function("incorrect_word", |b| bench_suggest(b, &FR_FR, "foobarbaz"));

    group.finish();
}

criterion_group!(benches, en_us, fr_fr);
criterion_main!(benches);
