{ pkgs, }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    (rust-bin.stable.latest.default.override {
      extensions = ["rust-src" "rust-analyzer" "clippy"];
    })
  ];
  RUST_BACKTRACE = "1";
  XDG_DATA_DIRS = with pkgs; lib.makeSearchPath "share" [hunspellDicts.en_US];
}
