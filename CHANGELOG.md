# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

* Added support for `Dictionary::suggest` and the `Suggester` type.

### Updated

* Changed the internal representation of word stems and flagsets for reduced
  memory consumption. [More...](https://the-mikedavis.github.io/posts/german-string-optimizations-in-spellbook/)

## [v0.1.0] - 2024-09-08

### Added

* Initial support for `Dictionary::new`, `Dictionary::check` and `Dictionary::add`
