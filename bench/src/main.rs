use std::hint::black_box;

use brunch::Bench;
use spellbook::Dictionary;

const SAMPLES: u32 = 500_000;

fn main() {
    let base = xdg::BaseDirectories::new().expect("Could not determine XDG directories");
    let (dic_path, aff_path) = match base.get_data_dirs().iter().find_map(|dir| {
        let subdir = dir.join("hunspell");
        if !subdir.is_dir() {
            return None;
        }

        let dic = subdir.join("en_US.dic");
        let aff = subdir.join("en_US.aff");
        if dic.is_file() && aff.is_file() {
            Some((dic, aff))
        } else {
            None
        }
    }) {
        Some((dic, aff)) => (dic, aff),
        None => {
            eprintln!("Could not find the en_US dictionary");
            std::process::exit(1);
        }
    };
    let dic_text = std::fs::read_to_string(dic_path).unwrap();
    let aff_text = std::fs::read_to_string(aff_path).unwrap();
    let dict = Dictionary::compile(&aff_text, &dic_text).unwrap();

    eprintln!("Starting benchmarks...");
    eprintln!();
    let now = std::time::Instant::now();
    brunch::benches!(
        inline:

        // Compilation
        Bench::new("Compile en_US")
            .run(|| Dictionary::compile(black_box(&aff_text), black_box(&dic_text))),
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
