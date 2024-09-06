# Spellbook

Spellbook is a Rust spellchecking library compatible with the Hunspell dictionary format.

```rust
fn main() {
    let aff = std::fs::read_to_string("en_US.aff").unwrap();
    let dic = std::fs::read_to_string("en_US.dic").unwrap();
    let dict = spellbook::Dictionary::new(&aff, &dic).unwrap();

    let word = std::env::args().nth(1).expect("expected a word to check");

    if dict.check(&word) {
        println!("{word:?} is in the dictionary.");
    } else {
        eprintln!("{word:?} is NOT in the dictionary.");
        std::process::exit(1);
    }
}
```

Spellbook is `no_std` and only requires [`hashbrown`] as a dependency. (Note that [`ahash`] is included by default, see the feature flags section below.) This may change in the future for performance tweaks like small-string optimizations and maybe `memchr` but the hope is to keep this library as lightweight as possible: new dependencies must considerably improve performance or correctness.

### Maturity

Spellbook is a work in progress and might see breaking changes to any part of the API as well as updates to the MSRV and dependencies.

Currently the `check` API works well for `en_US` - a relatively simple dictionary - though it should work reasonably well for most other dictionaries. Some dictionaries which use complex compounding directives may work less well. The `suggest` API is not yet implemented but is planned.

Spellbook should be considered to be in _alpha_. Part of the Hunspell test corpus has been successfully ported and there are a healthy number of unit tests, but there are certainly bugs to be found.

### Feature flags

The only feature flag currently is `default-hasher` which pulls in [`ahash`] and is enabled by default like the equivalent flag from [`hashbrown`]. A non-cryptographic hash significantly improves the time it takes to initialize a dictionary and check a word.

### How does it work?

For a more in depth overview, check out [`@zverok`]'s blog series [Rebuilding the spellchecker][zverok-blog].

Hunspell dictionaries are split into two files: `<lang>.dic` and `<lang>.aff`.
The `.dic` file has a listing of stems and flags associated with that stem. For example `en_US.dic` contains the word `adventure/DRSMZG` meaning that "adventure" is a stem in the dictionary with flags `D`, `R`, `S`, `M`, `Z` and `G`.
The `.aff` file contains a bunch of rules to use when determining if a word is correct or figuring out which words to suggest. The most intuitive of these are prefixes and suffixes. `en_US` contains suffixes like `D` and `R`:

```
SFX D Y 4
SFX D   0     d          e
SFX D   y     ied        [^aeiou]y
SFX D   0     ed         [^ey]
SFX D   0     ed         [aeiou]y

SFX R Y 4
SFX R   0     r          e
SFX R   y     ier        [^aeiou]y
SFX R   0     er         [aeiou]y
SFX R   0     er         [^ey]
```

Since "adventure" has these flags, these suffixes can be applied. The rules themselves are tables that define the flag (like `D`), what to strip from the end of the word (`0` for nothing), what to add to the end (`ied` for example) and under what condition the suffix applies (matches `[^aeiou]y` at the end for example). When checking a word like "adventured" you find any suffixes where the "add" portion of the suffix matches the ending of the word and check if the condition applies. The first clause of `D` applies since the "adventure" ends in 'e', and we add a 'd' to the end. When checking this happens in reverse. Starting with a word like "adventured" we strip the 'd' and check the condition. Similarly with `R`, the first clause matches because "adventure" ends with 'e' and we add an 'r', matching "adventurer".

Hunspell dictionaries use these prefixing and suffixing rules to compress the dictionary. Without prefixes and suffixes we'd need a big set of every possible conjugation of every word in the dictionary. That might be possible with the gigabytes of RAM we have today but it certainly isn't efficient.

Another way Hunspell dictionaries "compress" words like this is compounding. For example with the COMPOUNDRULE directive:

```
# compound rules:
# 1. [0-9]*1[0-9]th (10th, 11th, 12th, 56714th, etc.)
# 2. [0-9]*[02-9](1st|2nd|3rd|[4-9]th) (21st, 22nd, 123rd, 1234th, etc.)
COMPOUNDRULE 2
COMPOUNDRULE n*1t
COMPOUNDRULE n*mp
```

`en_US.dic` has words for digits like `0/nm`, `0th/pt`, `1/n1`, `1st/p`, etc. The COMPOUNDRULEs directive describes a regex-like pattern using flags and `*` (zero-or-more) and `?` (zero-or-one) modifiers. For example the first compound rule in the table `n*1t` allows a word like "10th": it matches the `n` flag zero times and then "1" (the stem of the `1` flag in the `.dic` file) and "0th". The `n*` modifier at the front allows adding any number of any other digit, so this rule also allows words like "110th" or "100000000th".

### Other docs

* An overview of [internals](./docs/internals.md)
* [Development and contributing notes](./docs/CONTRIBUTING.md)

### Credits

* [`@zverok`]'s [blog series on rebuilding Hunspell][zverok-blog] was an invaluable resource during early prototypes. The old [`spylls`](https://github.com/zverok/spylls)-like prototype can be found on the `spylls` branch.
* Ultimately [Nuspell](https://github.com/nuspell/nuspell)'s codebase became the reference for Spellbook though as C++ idioms mesh better with Rust than Python's. Nuspell's code is in great shape and is much more readable than Hunspell so for now Spellbook is essentially a Rust rewrite of Nuspell (though we may diverge in the future).
* The parser for `.dic` and `.aff` files is loosely based on [ZSpell](https://github.com/pluots/zspell).

[`hashbrown`]: https://github.com/rust-lang/hashbrown
[`ahash`]: https://github.com/tkaitchuck/aHash
[`@zverok`]: https://github.com/zverok
[zverok-blog]: https://zverok.space/spellchecker.html
