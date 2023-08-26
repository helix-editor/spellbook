use std::time::Instant;

use spellbook::Dictionary;

const EN_US_DIC: &str = include_str!("../vendor/en_US/en_US.dic");
const EN_US_AFF: &str = include_str!("../vendor/en_US/en_US.aff");

fn main() {
    let mut args = std::env::args().skip(1);
    let word = match args.next() {
        Some(arg) => arg,
        None => {
            eprintln!("Usage: check WORD");
            std::process::exit(1);
        }
    };

    let now = Instant::now();
    let dict = Dictionary::compile(EN_US_AFF, EN_US_DIC).unwrap();
    println!("Compiled the dictionary in {}ms", now.elapsed().as_millis());

    let now = Instant::now();
    if dict.check(&word) {
        println!(
            "\"{word}\" is in the dictionary (checked in {}µs)",
            now.elapsed().as_micros()
        );
    } else {
        eprintln!(
            "\"{word}\" is NOT in the dictionary (checked in {}µs)",
            now.elapsed().as_micros()
        );
        std::process::exit(1);
    }
}
