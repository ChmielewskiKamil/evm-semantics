let
  sources = import ./nix/sources.nix;
  pkgs = import sources."nixpkgs" {};

  kframework = import sources."k" { release = true; };
  inherit (kframework) llvm-backend;

  k = 
    if sources ? "haskell-backend" then 
      let
        haskell-backend-src = import sources."haskell-backend" {};
        inherit (haskell-backend-src) prelude-kore kore;
      in
        kframework.k.override {
          haskell-backend = kore;
          inherit prelude-kore;
        }
    else 
      kframework.k;

  haskell-backend = 
    if sources ? "haskell-backend" then 
      (import sources."haskell-backend" {}).kore
    else kframework.haskell-backend;
in
pkgs.mkShell {
  buildInputs = [
    k
    # kframework.z3
    llvm-backend
    haskell-backend
    pkgs.autoconf
    pkgs.cmake
    pkgs.clang_10
    pkgs.cryptopp.dev
    pkgs.elfutils
    pkgs.graphviz
    pkgs.openssl.dev
    pkgs.pkg-config
    pkgs.procps
    pkgs.protobuf
    pkgs.python38
    pkgs.secp256k1
    pkgs.solc
    pkgs.time
    pkgs.virtualenv
  ];
}
