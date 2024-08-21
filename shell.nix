{ pkgs, }:
let
  toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
in
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    (toolchain.override {
      extensions = ["rust-src" "clippy" "llvm-tools-preview"];
    })
    rust-analyzer
    cargo-flamegraph
    cargo-llvm-cov
  ];
  RUST_BACKTRACE = "1";
}
