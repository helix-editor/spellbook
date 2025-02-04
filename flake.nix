{
  description = "A Hunspell-like spell-checking library in Rust";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs =
    { nixpkgs, rust-overlay, ... }:
    let
      inherit (nixpkgs) lib;
      forEachSystem = lib.genAttrs lib.systems.flakeExposed;
    in
    {
      devShell = forEachSystem (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ rust-overlay.overlays.default ];
          };
          toolchain = pkgs.rust-bin.stable.latest.default;
        in
        pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            (toolchain.override {
              extensions = [
                "rust-src"
                "clippy"
                "llvm-tools-preview"
              ];
            })
            rust-analyzer
            cargo-flamegraph
            cargo-llvm-cov
            valgrind
          ];
          RUST_BACKTRACE = "1";
        }
      );
    };
}
