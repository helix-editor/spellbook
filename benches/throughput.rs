//! Throughput-oriented checking benchmark.
//!
//! Unlike `check.rs`, which times `check()` on a handful of individually-interesting words, this
//! benchmark walks a whole corpus of running prose and asks Criterion to report the result as a
//! throughput. Word segmentation (and, for the synthetic groups, corruption) happens outside the
//! timed loop: the corpus is tokenized once up front and the benchmark measures only the
//! `check()` calls over the resulting tokens.
//!
//! Groups:
//!
//! - `throughput/en_US`, `throughput/fr_FR`: clean prose, the common mostly-hits case. French
//!   is included because its much larger affix table stresses the affix-stripping machinery far
//!   harder than en_US.
//! - `throughput/en_US/scots`: Robert Burns' Scots verse checked against the en_US dictionary.
//!   The words are real, but ~22% land outside the dictionary, so this exercises the miss path
//!   (a miss forces `check()` to exhaust the affix-stripping search before returning `false`)
//!   with a natural distribution.
//! - `throughput/en_US/typos`: the clean en_US corpus with a tunable fraction of tokens
//!   deterministically corrupted. A sweep over the corruption rate shows how throughput degrades
//!   as misses climb. Typos are the nastiest miss: they resemble real words closely enough that
//!   many affix rules partially apply before the search fails.
//!
//! Each "clean"/"scots" group is reported two ways over the identical workload:
//!
//! - `bytes`: `Throughput::Bytes` over the bytes of the word tokens fed to `check()`.
//! - `words`: `Throughput::Elements` over the token count (words checked per second).
//!
//! The corpora under `benches/texts/` are public-domain prose/verse excerpts (Project Gutenberg),
//! with the Gutenberg boilerplate stripped:
//!
//! - `english.txt`: Jane Austen, _Pride and Prejudice_.
//! - `french.txt`: Voltaire, _Candide, ou l'optimisme_.
//! - `burns.txt`: Robert Burns, _Poems and Songs_ (Scots dialect).

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use once_cell::sync::Lazy;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");
const EN_US_CORPUS: &str = include_str!("texts/english.txt");
const SCOTS_CORPUS: &str = include_str!("texts/burns.txt");

const FR_FR_AFF: &str = include_str!("../vendor/fr_FR/fr.aff");
const FR_FR_DIC: &str = include_str!("../vendor/fr_FR/fr.dic");
const FR_FR_CORPUS: &str = include_str!("texts/french.txt");

type RandomState = foldhash::fast::FixedState;
/// A random seed from a sample run. The values aren't important here: just that they're constant.
const HASHER: RandomState = RandomState::with_seed(16553733157538299820);

static EN_US: Lazy<Dictionary<RandomState>> =
    Lazy::new(|| Dictionary::new_with_hasher(EN_US_AFF, EN_US_DIC, HASHER).unwrap());

static FR_FR: Lazy<Dictionary<RandomState>> =
    Lazy::new(|| Dictionary::new_with_hasher(FR_FR_AFF, FR_FR_DIC, HASHER).unwrap());

/// Split running text into word tokens the way a real spellchecker front-end would, then hand
/// whole tokens to `check()`. This runs once, outside the timed loop.
///
/// Apostrophes (both ASCII `'` and typographic `’`) and hyphens are kept inside tokens rather
/// than treated as boundaries, because the dictionaries declare them as word characters
/// (`WORDCHARS` in the `.aff` files) and `check()` is designed to handle them itself: it applies
/// `ICONV` (e.g. normalizing `’` to `'`) and `BREAK` (splitting on hyphens, stripping edge
/// apostrophes) per word. Splitting on them here would manufacture fragments like `l`/`esprit`
/// from `l’esprit` and bypass that machinery, under-exercising a real per-word cost. Tokens with
/// no alphanumeric character (stray dashes, lone quotes) are dropped.
fn tokenize(corpus: &str) -> Vec<&str> {
    corpus
        .split(|c: char| !(c.is_alphanumeric() || matches!(c, '\'' | '’' | '-')))
        .filter(|w| w.chars().any(char::is_alphanumeric))
        .collect()
}

/// Deterministically corrupt a word so it (usually) misses the dictionary: transpose the two
/// middle characters, or double a lone character. RNG-free so the corpus is identical run-to-run.
fn corrupt(word: &str) -> String {
    let mut cs: Vec<char> = word.chars().collect();
    let n = cs.len();
    if n >= 2 {
        cs.swap(n / 2 - 1, n / 2);
    } else {
        cs.push(cs[0]);
    }
    cs.into_iter().collect()
}

fn bench_lang(c: &mut Criterion, name: &str, dict: &Dictionary<RandomState>, corpus: &str) {
    let words = tokenize(corpus);
    let checked_bytes: u64 = words.iter().map(|w| w.len() as u64).sum();

    let mut group = c.benchmark_group(format!("throughput/{name}"));

    group.throughput(Throughput::Bytes(checked_bytes));
    group.bench_function("bytes", |b| {
        b.iter(|| {
            for &word in &words {
                black_box(dict.check(black_box(word)));
            }
        })
    });

    group.throughput(Throughput::Elements(words.len() as u64));
    group.bench_function("words", |b| {
        b.iter(|| {
            for &word in &words {
                black_box(dict.check(black_box(word)));
            }
        })
    });

    group.finish();
}

/// Sweep the synthetic corruption rate over the clean en_US corpus, reporting words/sec at each
/// rate so the degradation as misses climb is visible. Corruption happens outside the timed loop.
fn bench_typos(c: &mut Criterion, dict: &Dictionary<RandomState>, corpus: &str) {
    let words = tokenize(corpus);

    let mut group = c.benchmark_group("throughput/en_US/typos");
    group.throughput(Throughput::Elements(words.len() as u64));

    for pct in [0u32, 25, 50, 100] {
        // Corrupt every (100/pct)th token; pct == 0 leaves the corpus clean.
        let corrupted: Vec<String> = words
            .iter()
            .enumerate()
            .map(|(i, w)| {
                if pct != 0 && i % (100 / pct) as usize == 0 {
                    corrupt(w)
                } else {
                    (*w).to_string()
                }
            })
            .collect();

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{pct}pct")),
            &corrupted,
            |b, toks| {
                b.iter(|| {
                    for word in toks {
                        black_box(dict.check(black_box(word)));
                    }
                })
            },
        );
    }

    group.finish();
}

fn benches(c: &mut Criterion) {
    bench_lang(c, "en_US", &EN_US, EN_US_CORPUS);
    bench_lang(c, "fr_FR", &FR_FR, FR_FR_CORPUS);
    bench_lang(c, "en_US/scots", &EN_US, SCOTS_CORPUS);
    bench_typos(c, &EN_US, EN_US_CORPUS);
}

criterion_group!(bench, benches);
criterion_main!(bench);
