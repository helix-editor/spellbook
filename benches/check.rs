#![feature(test)]

extern crate test;

use once_cell::sync::Lazy;
use spellbook::Dictionary;
use test::{black_box, Bencher};

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

type RandomState = foldhash::fast::FixedState;
/// A random seed from a sample run. The values aren't important here: just that they're constant.
/// We don't want the benchmark outputs to reflect random changes to the seed.
const HASHER: RandomState = RandomState::with_seed(16553733157538299820);

static EN_US: Lazy<Dictionary<RandomState>> =
    Lazy::new(|| Dictionary::new_with_hasher(EN_US_AFF, EN_US_DIC, HASHER).unwrap());

#[bench]
fn in_dictionary_word(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("earth")))
}

#[bench]
fn number(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("8675,309.0")))
}

#[bench]
fn word_with_suffix(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("earthly")))
}

#[bench]
fn word_with_prefix(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("unearth")))
}

#[bench]
fn word_with_prefix_and_suffix(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("unearthed")))
}

#[bench]
fn incorrect_prefix(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("reearth")))
}

#[bench]
fn uppercase_in_dictionary_word(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("EARTH")))
}

#[bench]
fn titlecase_in_dictionary_word(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("Earth")))
}

#[bench]
fn breaks(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("light-weight-like")))
}

#[bench]
fn compound_word(b: &mut Bencher) {
    b.iter(|| EN_US.check(black_box("20000th")))
}
