use std::time::Instant;

use spellbook::Dictionary;
use xdg::BaseDirectories;

fn main() {
    let mut args = std::env::args().skip(1);
    let arg1 = match args.next() {
        Some(arg) => arg,
        None => {
            eprintln!("Usage: check [LANG] WORD");
            std::process::exit(1);
        }
    };
    let (lang, word) = match args.next() {
        Some(arg2) => (arg1, arg2),
        None => ("en_US".to_string(), arg1),
    };

    let base = BaseDirectories::new().expect("Could not determine XDG directories");
    let (dic_path, aff_path) = match base.get_data_dirs().iter().find_map(|dir| {
        let subdir = dir.join("hunspell");
        if !subdir.is_dir() {
            return None;
        }

        let dic = subdir.join(format!("{lang}.dic"));
        let aff = subdir.join(format!("{lang}.aff"));
        if dic.is_file() && aff.is_file() {
            Some((dic, aff))
        } else {
            None
        }
    }) {
        Some((dic, aff)) => (dic, aff),
        None => {
            eprintln!("Could not find the {lang} dictionary");
            std::process::exit(1);
        }
    };
    let dic_text = std::fs::read_to_string(dic_path).unwrap();
    let aff_text = std::fs::read_to_string(aff_path).unwrap();

    let now = Instant::now();
    let dict = Dictionary::compile(&aff_text, &dic_text).unwrap();
    println!(
        "Compiled the {lang} dictionary in {}ms",
        now.elapsed().as_millis()
    );

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
