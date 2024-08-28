# Spellbook

Spellbook is a Rust spellchecker library compatible with the Hunspell dictionary format.

```rust
fn main() {
    let aff = std::fs::read_to_string("en_US.aff").unwrap();
    let dic = std::fs::read_to_string("en_US.dic").unwrap();
    let dict = spellbook::Dictionary::new_with_hasher(&dic, &aff, ahash::RandomState::new());

    let word = std::env::args().nth(1).expect("expected a word to check");

    if dict.check(&word) {
        println!("{word:?} is in the dictionary.");
    } else {
        eprintln!("{word:?} is NOT in the dictionary.");
        std::process::exit(1);
    }
}
```

Spellbook is `no_std` and carries only [`hashbrown`] as a dependency. This may change in the future for performance tweaks like small-string optimizations and maybe `memchr` but the hope is to keep this library as lightweight as possible.

### Maturity

Spellbook is a work in progress and might see breaking changes to any part of the API as well as updates to the MSRV and dependencies.

Currently the `check` API works well for `en_US` - a relatively simple dictionary - though it should work reasonably well for most other dictionaries. Some dictionaries which use complex compounding directives may work less well. The `suggest` API is not yet implemented but is planned.

Spellbook should be considered to be in _alpha_. Part of the Hunspell test corpus has been ported and there are a healthy number of unit tests, but there are certainly bugs to be found.

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

Since "adventure" has these flags, these suffixes can be applied. The rules themselves are tables that define the flag (like `D`), what to strip from the end of the word (`0` for nothing), what to add to the end (`ied` for example) and under what condition the suffix applies (matches `[^aeiou]y` at the end for example). When checking a word like "adventured" you find any suffixes where the "add" portion of the suffix matches the ending of the word and check if the condition applies. The first clause of `D` applies since the "adventure" ends in 'e', and we add a 'd' to the end. When checking this happens in reverse. Starting with a word like "adventured" we strip the "d" and check the condition. Similarly with `R`, the first clause matches because "adventure" ends with 'e' and we add an 'r', matching "adventurer".

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

### Internals

There are a few key data structures that power spellbook and make lookup fast.

##### Boxed slices

By default Spellbook prefers boxed slices (`Box<[T]>`) and boxed strs (`Box<str>`) rather than their mutable counterparts `Vec<T>` and `String`. Boxed slices are basically the same but are immutable once created. They also discard any excess capacity and don't need to track capacity, saving a very small amount of memory per instance. That memory adds up though across all of the words in the dictionary. For some quick napkin math, this saves at least 392,464 bytes for the word list in `en_US` on a 64 bit target: 4 bytes for the stem's capacity field and another 4 bytes for the flag set's capacity field for each of the 49,058 words in `en_US.dic`.

##### Flag sets

Words in the dictionary are associated with any number of flags, like `adventure/DRSMZG` mentioned above. The order of the flags as written in the dictionary isn't important. We need a way to look up whether a flag exists in that set quickly. The right tool for the job might seem like a `HashSet<Flag>` or a `BTreeSet<Flag>`. Those are mutable though so they carry some extra overhead. A dictionary contains many many flag sets and the overhead adds up. So what we use instead is a sorted `Box<[Flag]>` and look up flags with `slice::binary_search`.

Binary searching a small slice is typically a tiny bit slower than `slice::contains` but we prefer `slice::binary_search` for its consistent performance. See [`examples/bench-slice-contains.rs`](./examples/bench-slice-contains.rs) for more details.

##### Flags

While we're talking about flags, the internal representation in Spellbook is a `NonZeroU16`. Flags are always non-`0` so `NonZeroU16` is appropriate. `NonZeroU16` also has a layout optimization in Rust such that an `Option<NonZeroU16>` is represented by 16 bits: you don't pay for the `Option`. This optimization isn't useful when flags are in flag sets but flags are also used in `.aff` files to mark stems as having special properties. For example `en_US` uses `ONLYINCOMPOUND c` to declare that stems in the dictionary with the `c` flag are only valid when used in a compound, for example `1th/tc`, `2th/tc` or `3th/tc`. These stems are only meant to be combined in a compound like "11th", "12th" or "13th" and aren't valid words themselves.

By default, flags are encoded in a dictionary with the `UTF-8` flag type. For `en_US` that means that each character after the `/` in a word in the dictionary and any flags declared in `en_US.aff` are converted to a `u16` (and then `NonZeroU16`). A 16 bit integer can't actually fit all UTF-8 codepoints (UTF-8 codepoints may be up to 32 bits) but the lower 16 bits of UTF-8 are more than sufficient for declaring flags: flags are only used to specify properties with the `.aff` file rather than stems. There are other encoding for flags used by some dictionaries. See the `FlagType` enum for more details.

##### Word list

The word list is one of the two central data structures. It stores the set of `(stem, flag_set)`. We need to look up whether a word is in the dictionary (and what flags it has) very quickly. A natural choice might be `HashMap<String, FlagSet>` or `BTreeSet<String, FlagSet>`. Unlike flag sets and boxed slices and strs mentioned above, it's ok for this type to be mutable. There's only one instance of it in a dictionary and it might make sense to add an API to add words to the dictionary, to cover the use-case of adding to a personal dictionary interactively for example. Instead the snag with this type is that there can be duplicate stems in the dictionary with different flag sets. Merging the flag sets together isn't correct: the combination of flags might allow one prefix/suffix to apply but not work in a compounds while another entry provides a different prefix/suffix which can compound.

So what we need is something closer to `HashMap<String, Vec<FlagSet>>`. The extra `Vec` is more overhead though that isn't necessary in most cases since duplicate stems are fairly rare. In other languages like C++ this is where a [multi map](https://en.cppreference.com/w/cpp/container/unordered_multimap) might fit. It's the same idea as a hash map but allows for duplicate keys. Building a type like this in Rust is actually pretty straightforward with the [`hashbrown`] raw API which exposes enough internals to build a new hash table type. The table's `Iterator` implementation is identical. Insertion is slightly simpler: we don't need to check if the key is already in the map, we can just blindly insert. Reading from the table works very similarly to `HashMap::get`. Lookup in a regular hash map can stop searching the table when the first entry matching the key is found. For a multi map though we continue to look up until we find an entry that doesn't match.

See the implementation details for this in [`src/hash_bag.rs`](./src/hash_bag.rs).

##### Affix index

Affixes (i.e. prefixes and suffixes) are stored in an "index" that allows quick lookup. For example `en_US` has prefixes like these:

```
PFX C Y 1
PFX C   0     de          .

PFX E Y 1
PFX E   0     dis         .
```

Which might apply to a stem in the dictionary like `pose/CAKEGDS` to allow words "depose" and "dispose". When checking "depose" we look up in the set of prefixes to find any where the "add" port are prefixes of the input word (`"depose".starts_with("de")`).

A [prefix tree](https://en.wikipedia.org/wiki/Trie) would allow very quick lookup. Trees and graph-like structures are not the most straightforward things to write in Rust though. Luckily Nuspell has a trick for this type which works well in Rust. Instead of a tree, we collect the set of prefixes into a sorted `Box<[Prefix]>` table. We can then binary search based on whether a prefix matches (`str::starts_with`). There are some additional optimizations like an extra lookup table that maps the first character in a prefix to the starting index in the `Box<[Prefix]>` table so that we can jump to the right region of the table quickly.

### Credits

* [`@zverok`]'s [blog series on rebuilding Hunspell][zverok-blog] was an invaluable resource during early prototypes. The old [`spylls`](https://github.com/zverok/spylls)-like prototype can be found on the `spylls` branch.
* Ultimately [Nuspell](https://github.com/nuspell/nuspell)'s codebase became the reference for Spellbook though as C++ idioms mesh better with Rust than Python's. Nuspell's code is in great shape and is much more readable than Hunspell so for now Spellbook is essentially a Rust rewrite of Nuspell (though we may diverge in the future).
* The parser for `.dic` and `.aff` files is loosely based on [ZSpell](https://github.com/pluots/zspell).

[`hashbrown`]: https://github.com/rust-lang/hashbrown
[`@zverok`]: https://github.com/zverok
[zverok-blog]: https://zverok.space/spellchecker.html
