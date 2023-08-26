use std::hint::black_box;

use brunch::Bench;
use spellbook::Dictionary;

const EN_US_DIC: &str = include_str!("../../vendor/en_US/en_US.dic");
const EN_US_AFF: &str = include_str!("../../vendor/en_US/en_US.aff");

const SAMPLES: u32 = 500_000;

fn main() {
    let dict = Dictionary::compile(EN_US_AFF, EN_US_DIC).unwrap();

    eprintln!("Starting benchmarks...");
    eprintln!();
    let now = std::time::Instant::now();
    brunch::benches!(
        inline:

        // Compilation
        Bench::new("Compile en_US")
            .run(|| Dictionary::compile(black_box(EN_US_AFF), black_box(EN_US_DIC))),
        Bench::spacer(),

        // Checking
        Bench::new("In-dictionary word (\"drink\")")
            .with_samples(SAMPLES)
            .run(|| dict.check(black_box("drink"))),
        Bench::new("Word with a suffix (\"drinkable\")")
            .with_samples(SAMPLES)
            .run(|| dict.check(black_box("drinkable"))),
        Bench::new("Multi-affix (\"undrinkable\")")
            .with_samples(SAMPLES)
            .run(|| dict.check(black_box("undrinkable"))),
        Bench::new("Incorrect prefix (\"undrink\")")
            .with_samples(SAMPLES)
            .run(|| dict.check(black_box("undrink"))),
        Bench::new("Breaks (\"light-weight-like\")")
            .with_samples(SAMPLES)
            .run(|| dict.check(black_box("light-weight-like"))),
    );
    eprintln!("Finished in {:.1}s", now.elapsed().as_secs_f64());
}
