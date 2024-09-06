# Internals

There are a few key data structures that power Spellbook and make lookup fast and memory efficient.

### Boxed slices

By default Spellbook prefers boxed slices (`Box<[T]>`) and boxed strs (`Box<str>`) rather than their mutable counterparts `Vec<T>` and `String`. Boxed slices can be used the same but are immutable once created. You can push to a `Vec` but not a `Box<[T]>` for example. They also discard any excess capacity and don't need to track capacity, saving a very small amount of memory per instance. That memory adds up though across all of the words in the dictionary.

For some quick napkin math, this saves at least 392,464 bytes for the word list in `en_US` on a 64 bit target: 4 bytes for the stem's capacity field and another 4 bytes for the flag set's capacity field for each of the 49,058 words in `en_US.dic`. In practice we can measure the difference with Valgrind's [DHAT](https://valgrind.org/docs/manual/dh-manual.html) tool. If we switch Spellbook's `WordList` type to store `String`s and `Vec<Flag>`s instead of `Box<str>`s and `Box<[Flag]>`s, I see the total heap bytes allocated in a run of `./target/debug/examples/check hello` rise from 3MB to 4MB.

### Flag sets

```rust
struct FlagSet(Box<[Flag]>);
```

Words in the dictionary are associated with any number of flags, like `adventure/DRSMZG` mentioned above. The order of the flags as written in the dictionary isn't important. We need a way to look up whether a flag exists in that set quickly. The right tool for the job might seem like a `HashSet<Flag>` or a `BTreeSet<Flag>`. Those are mutable though so they carry some extra overhead. A dictionary contains many many flag sets and the overhead adds up. So what we use instead is a sorted `Box<[Flag]>` and look up flags with `slice::binary_search`.

Binary searching a small slice is typically a tiny bit slower than `slice::contains` but we prefer `slice::binary_search` for its consistent performance. See [`examples/bench-slice-contains.rs`](./examples/bench-slice-contains.rs) for more details.

### Flags

```rust
type Flag = core::num::NonZeroU16;
```

While we're talking about flags, the internal representation in Spellbook is a `NonZeroU16`. Flags are always non-`0` so `NonZeroU16` is appropriate. `NonZeroU16` also has a layout optimization in Rust such that an `Option<NonZeroU16>` is represented by 16 bits: you don't pay for the `Option`. This optimization isn't useful when flags are in flag sets but flags are also used in `.aff` files to mark stems as having special properties. For example `en_US` uses `ONLYINCOMPOUND c` to declare that stems in the dictionary with the `c` flag are only valid when used in a compound, for example `1th/tc`, `2th/tc` or `3th/tc`. These stems are only meant to be combined in a compound like "11th", "12th" or "13th" and aren't valid words themselves. Internally Spellbook keeps a bunch of these `Option<Flag>`s so the layout optimization saves some space.

By default, flags are encoded in a dictionary with the `UTF-8` flag type. For `en_US` that means that each character after the `/` in a word in the dictionary and any flags declared in `en_US.aff` are converted to a `u16` (and then `NonZeroU16`). A 16 bit integer can't actually fit all UTF-8 codepoints (UTF-8 codepoints may be up to 32 bits) but the lower 16 bits of UTF-8 are more than sufficient for declaring flags: flags are only used to specify properties with the `.aff` file rather than stems. There are other encoding for flags used by some dictionaries. See the `FlagType` enum for more details.

### Word list

```rust
type WordList<S> = HashBag<Box<str>, FlagSet, S>;
```

The word list is one of the two central data structures. It stores the set of `(stem, flag_set)`. We need to look up whether a word is in the dictionary (and what flags it has) very quickly. A natural choice might be `HashMap<String, FlagSet>` or `BTreeSet<String, FlagSet>`. Unlike flag sets and boxed slices and strs mentioned above, it's ok for this type to be mutable. There's only one instance of it in a dictionary and it might make sense to add an API to add words to the dictionary, to cover the use-case of adding to a personal dictionary interactively for example. Instead the snag with this type is that there can be duplicate stems in the dictionary with different flag sets. Merging the flag sets together isn't correct: the combination of flags might allow one prefix/suffix to apply but not work in a compounds while another entry provides a different prefix/suffix which can compound.

So what we need is something closer to `HashMap<String, Vec<FlagSet>>`. The extra `Vec` is more overhead though that isn't necessary in most cases since duplicate stems are fairly rare. In other languages like C++ this is where a [multi map](https://en.cppreference.com/w/cpp/container/unordered_multimap) might fit. It's the same idea as a hash map but allows for duplicate keys. Building a type like this in Rust is actually pretty straightforward with the [`hashbrown`] raw API which exposes enough internals to build a new hash table type. The table's `Iterator` implementation is identical. Insertion is slightly simpler: we don't need to check if the key is already in the map, we can just blindly insert. Reading from the table works very similarly to `HashMap::get`. Lookup in a regular hash map can stop searching the table when the first entry matching the key is found. For a multi map though we continue to look up until we find an entry that doesn't match.

See the implementation details for this in [`src/hash_bag.rs`](./src/hash_bag.rs).

### Affix index

Affixes (i.e. prefixes and suffixes) are stored in an "index" that allows quick lookup. For example `en_US` has prefixes like these:

```
PFX C Y 1
PFX C   0     de          .

PFX E Y 1
PFX E   0     dis         .
```

Which might apply to a stem in the dictionary like `pose/CAKEGDS` to allow words "depose" and "dispose". When checking "depose" we look up in the set of prefixes to find any where the "add" port are prefixes of the input word (`"depose".starts_with("de")`).

A [prefix tree](https://en.wikipedia.org/wiki/Trie) would allow very quick lookup. Trees and graph-like structures are not the most straightforward things to write in Rust though. Luckily Nuspell has a trick for this type which works well in Rust. Instead of a tree, we collect the set of prefixes into a `Box<[Prefix]>` table sorted by the "add" part of a prefix/suffix ("de" or "dis" above, for example). We can then binary search based on whether a prefix matches (`str::starts_with`). There are some additional optimizations like an extra lookup table that maps the first character in a prefix to the starting index in the `Box<[Prefix]>` table so that we can jump to the right region of the table quickly.
