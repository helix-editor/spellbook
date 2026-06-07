use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use foldhash::fast::FixedState;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

/// A random seed from a sample run. The values aren't important here: just that they're constant.
/// We don't want the benchmark outputs to reflect random changes to the seed.
const HASHER: FixedState = FixedState::with_seed(16553733157538299820);

fn compilation(c: &mut Criterion) {
    c.bench_function("compilation/en_US", |b| {
        b.iter(|| Dictionary::new_with_hasher(black_box(EN_US_AFF), black_box(EN_US_DIC), HASHER))
    });
}

criterion_group!(benches, compilation);
criterion_main!(benches);
