# master

```
Running benches/check.rs (target/release/deps/check-1d1858f62ff0a79c)

running 10 tests
test breaks                       ... bench:         888.95 ns/iter (+/- 15.54)
test compound_word                ... bench:         732.08 ns/iter (+/- 90.39)
test in_dictionary_word           ... bench:          64.62 ns/iter (+/- 2.79)
test incorrect_prefix             ... bench:         500.31 ns/iter (+/- 11.10)
test number                       ... bench:          35.01 ns/iter (+/- 5.19)
test titlecase_in_dictionary_word ... bench:         345.68 ns/iter (+/- 12.74)
test uppercase_in_dictionary_word ... bench:         597.55 ns/iter (+/- 14.71)
test word_with_prefix             ... bench:         184.07 ns/iter (+/- 8.25)
test word_with_prefix_and_suffix  ... bench:         355.57 ns/iter (+/- 8.88)
test word_with_suffix             ... bench:          65.53 ns/iter (+/- 2.39)

Running benches/compilation.rs (target/release/deps/compilation-7f7577ace9477d8d)

running 1 test
test compile_en_US ... bench:   6,768,623.00 ns/iter (+/- 49,825.47)
```

# hamt

```
Running benches/check.rs (target/release/deps/check-1d1858f62ff0a79c)

running 10 tests
test breaks                       ... bench:       1,589.67 ns/iter (+/- 35.21)
test compound_word                ... bench:         857.74 ns/iter (+/- 21.73)
test in_dictionary_word           ... bench:          77.82 ns/iter (+/- 1.48)
test incorrect_prefix             ... bench:         636.82 ns/iter (+/- 12.74)
test number                       ... bench:          32.13 ns/iter (+/- 0.42)
test titlecase_in_dictionary_word ... bench:         403.29 ns/iter (+/- 9.73)
test uppercase_in_dictionary_word ... bench:         684.22 ns/iter (+/- 16.34)
test word_with_prefix             ... bench:         206.50 ns/iter (+/- 9.12)
test word_with_prefix_and_suffix  ... bench:         421.80 ns/iter (+/- 10.47)
test word_with_suffix             ... bench:          80.90 ns/iter (+/- 0.53)

Running benches/compilation.rs (target/release/deps/compilation-7f7577ace9477d8d)

running 1 test
test compile_en_US ... bench:  22,202,202.50 ns/iter (+/- 148,166.54)
```
