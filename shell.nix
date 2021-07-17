with import <nixpkgs> {};
pkgs.mkShell {
  buildInputs = [
    pkgs.idris2
  ];
}
