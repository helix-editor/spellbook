use std::hint::black_box;

use brunch::Bench;
use once_cell::sync::OnceCell;
use spellbook::Dictionary;

const EN_US_DIC: &str = include_str!("../../vendor/en_US/en_US.dic");
const EN_US_AFF: &str = include_str!("../../vendor/en_US/en_US.aff");

const SAMPLES: u32 = 500_000;

fn en_us() -> &'static Dictionary<ahash::RandomState> {
    static EN_US: OnceCell<Dictionary<ahash::RandomState>> = OnceCell::new();
    EN_US.get_or_init(|| {
        Dictionary::new_with_hasher(EN_US_DIC, EN_US_AFF, ahash::RandomState::new()).unwrap()
    })
}

brunch::benches!(
    // Compilation
    Bench::new("Compile en_US").run(|| Dictionary::new_with_hasher(
        black_box(EN_US_DIC),
        black_box(EN_US_AFF),
        ahash::RandomState::new()
    )),
    Bench::spacer(),
    // Checking
    Bench::new("In-dictionary word (\"drink\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("drink"))),
    Bench::new("Word with a suffix (\"drinkable\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("drinkable"))),
    Bench::new("Multi-affix (\"undrinkable\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("undrinkable"))),
    Bench::new("Incorrect prefix (\"undrink\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("undrink"))),
    Bench::new("Breaks (\"light-weight-like\")")
        .with_samples(SAMPLES)
        .run_seeded_with(en_us, |dict| dict.check(black_box("light-weight-like"))),
);
