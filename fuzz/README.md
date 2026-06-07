# Fuzzing

This directory holds [`cargo-fuzz`] (libFuzzer) targets. Spellbook parses untrusted `.aff`/`.dic`
files and checks arbitrary words, so these targets assert that it never panics on hostile input.

Install the runner once with `cargo install cargo-fuzz`. It requires a nightly toolchain.

Targets:

- `parse_dictionary`: feeds arbitrary bytes to `Dictionary::new` (the `.aff` and `.dic` halves are
  split on the first NUL byte). Confirms the parser only ever returns `Ok`/`Err`.
- `check_word`: feeds arbitrary words to `check` and `suggest` against the `en_US` dictionary.
  Exercises the char-boundary slicing and the suggester's in-place `unsafe` buffer rewrites.

Run a target:

```sh
cargo +nightly fuzz run parse_dictionary
cargo +nightly fuzz run check_word
```

Time-box a run (useful in CI):

```sh
cargo +nightly fuzz run parse_dictionary -- -max_total_time=60
```
