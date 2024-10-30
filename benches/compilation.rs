#![feature(test)]

extern crate test;

use ahash::RandomState;
use spellbook::Dictionary;
use test::{black_box, Bencher};

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

/// A random seed from a sample run. The values aren't important here: just that they're constant.
/// We don't want the benchmark outputs to reflect random changes to the seed.
const HASHER: RandomState = RandomState::with_seeds(
    16553733157538299820,
    16824988918979132550,
    1196480943954226392,
    17486544621636611338,
);

#[bench]
#[allow(non_snake_case)]
fn compile_en_US(b: &mut Bencher) {
    b.iter(|| Dictionary::new_with_hasher(black_box(EN_US_AFF), black_box(EN_US_DIC), HASHER))
}
