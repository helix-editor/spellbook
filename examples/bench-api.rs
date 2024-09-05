use std::hint::black_box;

use ahash::RandomState;
use brunch::Bench;
use once_cell::sync::OnceCell;
use spellbook::Dictionary;

const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");
const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");

const SAMPLES: u32 = 500_000;

/// A random seed from a sample run. The values aren't important here: just that they're constant.
/// We don't want the benchmark outputs to reflect random changes to the seed.
const HASHER: RandomState = RandomState::with_seeds(
    16553733157538299820,
    16824988918979132550,
    1196480943954226392,
    17486544621636611338,
);

fn en_us() -> &'static Dictionary<RandomState> {
    static EN_US: OnceCell<Dictionary<RandomState>> = OnceCell::new();
    EN_US.get_or_init(|| Dictionary::new_with_hasher(EN_US_AFF, EN_US_DIC, HASHER).unwrap())
}

brunch::benches!(
    // Compilation
    Bench::new("Compile en_US").run(|| Dictionary::new_with_hasher(
        black_box(EN_US_AFF),
        black_box(EN_US_DIC),
        HASHER,
    )),
    Bench::spacer(),
    // Checking
    Bench::new("In-dictionary word (\"earth\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("earth"))),
    Bench::new("Number (\"8675,309.0\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("8675,309.0"))),
    Bench::new("Word with suffix (\"earthly\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("earthly"))),
    Bench::new("Word with prefix (\"unearth\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("unearth"))),
    Bench::new("Word with prefix and suffix (\"unearthed\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("unearthed"))),
    Bench::new("Incorrect prefix (\"reearth\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("reearth"))),
    Bench::new("UPPERCASE in-dictionary word (\"EARTH\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("EARTH"))),
    Bench::new("Titlecase in-dictionary word (\"Earth\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("Earth"))),
    Bench::new("Breaks (\"light-weight-like\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("light-weight-like"))),
    Bench::new("Compound word (\"20000th\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("20000th"))),
);
