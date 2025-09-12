# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- ## [Unreleased] -->

## [v0.3.5] - 2025-09-12

### Fixed

* [UTF-8 BOM](https://en.wikipedia.org/wiki/Byte_order_mark#UTF-8) characters are
  now stripped from dictionary text if present.
* The `#` character is no special-cased as a comment, fixing parsing of some
  dictionaries `en_GB`.
* Version requirements on Hashbrown and Foldhash have been loosened.

## [v0.3.4] - 2025-04-30

### Fixed

* Fixed a panic similar to the one fixed in v0.3.3 but within the checker instead
  of the suggester.
    * This panic could happen in dictionaries which used `REP` patterns with end
      anchors (i.e. the first word after `REP` ends in `$`) which also sets
      `CHECKCOMPOUNDREP` and other related compounding rules.

## [v0.3.3] - 2025-04-21

### Fixed

* Fixed a panic possible in the suggester when suggesting corrections for a word with
  non-ASCII characters near the end in dictionaries with replacement patterns with end
  anchors.
    * For example `caféx` in a french dictionary which has a `REP è$ e` rule.

## [v0.3.2] - 2025-04-15

### Fixed

* Aligned parsing of flags with Hunspell. This fixes cases where a dictionary would
  use non-ASCII characters for flags without setting `FLAG UTF-8`.

## [v0.3.1] - 2025-03-11

### Fixed

* Fixed handling of Unicode flags which are represented by more than one code
  unit in UTF-16 representation, for example emoji such as '🔭'.

## [v0.3.0] - 2025-02-04

### Added

* Exposed the `Checker` type.
* Added `Checker::check_lower_as_title` and `Checker::check_lower_as_upper` to
  configure the checker to try lowercase words as title and/or uppercase.

### Changed

* The `default-hasher` feature flag now uses [`foldhash`](https://github.com/orlp/foldhash)
  instead of [`ahash`](https://github.com/tkaitchuck/aHash).

## [v0.2.0] - 2024-11-18

### Added

* Added support for `Dictionary::suggest` and the `Suggester` type.

### Updated

* Changed the internal representation of word stems and flagsets for reduced
  memory consumption. [More...](https://the-mikedavis.github.io/posts/german-string-optimizations-in-spellbook/)

## [v0.1.0] - 2024-09-08

### Added

* Initial support for `Dictionary::new`, `Dictionary::check` and `Dictionary::add`
