with import <nixpkgs> {};
pkgs.mkShell {
  buildInputs = [
    (callPackage (import ./idris2.nix) {})
  ];
}
