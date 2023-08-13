{ pkgs, }:
let
  toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
in
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    (toolchain.override {
      extensions = ["rust-src" "clippy"];
    })
    rust-analyzer
    cargo-flamegraph
  ];
  RUST_BACKTRACE = "1";
  XDG_DATA_DIRS = with pkgs; lib.makeSearchPath "share" [hunspellDicts.en_US];
}
