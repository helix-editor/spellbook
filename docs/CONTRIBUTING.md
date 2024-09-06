# Contributing

New to contributing to projects on GitHub? GitHub provides [getting started documentation](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests) for contributing via pull requests (PRs).

## Installing Rust

To build and test Spellbook you will need a Rust compiler and the `cargo` command. [rustup](https://rustup.rs/) is the recommended way to install Rust. It manages versions and components of Rust like cargo and clippy and it will install the expected versions of each component specified in the `rust-toolchain.toml` file in the root of the repository. Install `rustup` as [the Rust documentation recommends](https://www.rust-lang.org/tools/install).

You may also install Rust through a system package manager but it might not be the version pinned in `rust-toolchain.toml`. Also see the [MSRV](#msrv) section below.

If you use [Nix or NixOS](https://nixos.org/) you can use the [flake](https://nixos.wiki/wiki/flakes) via `nix develop` or `shell.nix` via `nix-shell` in the repository root to spawn a shell with the necessary dependencies. Using Nix is entirely optional and is only provided for convenience.

## MSRV

Spellbook keeps an intentionally low <b>m</b>inimum <b>s</b>upported <b>R</b>ust <b>v</b>ersion for the sake of easy compatibility with consuming applications.

The MSRV should never rise higher than allowed by [Mozilla's Firefox MSRV policy](https://firefox-source-docs.mozilla.org/writing-rust-code/update-policy.html) and should lag behind by as many more versions as is practical.

## Linting

Spellbook's CI expects the following lints to pass:

* `cargo fmt --check` - the project is formatted
* `cargo clippy` - there are no lints with default features enabled
* `cargo clippy --no-default-features` - there are no lints with no default features
* `cargo doc --document-private-items` - documentation can be generated without warnings

## Testing

Run the testsuite with:

```
cargo test
```

The testsuite has three parts:

* Unit tests. These are in `src/**.rs` in `test` modules at the end of each file.
* Doc tests. These are in markdown codefences in documentation comments (comments starting with `///`).
* "Legacy" tests. These tests live under `tests/legacy/` and are run by `tests/legacy.rs`. These cases are ported originally from the Hunspell codebase and should not be added to unless an equivalent test exists upstream in Hunspell or Nuspell.

### Adding a test case

Avoid adding a test case under `tests/legacy/`. Instead if you're fixing a bug with the checker for example, add a unit test case to the `test` module at the bottom of `src/checker.rs`. Follow examples in that module for creating small dictionaries within the unit test function.

### Generating code coverage reports

You can generate a human readable coverage report using [`cargo-llvm-cov`](https://github.com/taiki-e/cargo-llvm-cov). With that tool installed:

```
cargo llvm-cov --html test
```

For this to work you also need `llvm-tools-preview`. This component is specified in `rust-toolchain.toml` so it should be installed by `rustup`. `cargo-llvm-cov` and `llvm-tools-preview` are included in the Nix development shell for convenience.

## Benchmarking

There are a few benchmarks in the `examples/` directory built with [`brunch`](https://github.com/Blobfolio/brunch). The main benchmark to pay attention to is `bench-api` which covers some common cases of Spellbook usage. Run `cargo run --release --example bench-api` before and after a change to see the difference in timings. Note that the timing each benchmark might vary slightly between runs: the timing of a case swaying plus or minus 5% is not unusual. Run the benchmark multiple times to get a feel for how a change impacted performance.
