{ nixpkgs ? import <nixpkgs> { }
, ghcVersion ? "ghc8107"}:

let
  # Create a modified Haskell package set with our app in it
  hpkgs = nixpkgs.haskellPackages.override {
    overrides = hself: hsuper: {
      eigencompanion = hself.callCabal2nix "eigencompanion-PoC" ./. { };
      eigen = nixpkgs.haskell.lib.doJailbreak hsuper.eigen;
      # beam-postgres = nixpkgs.haskell.lib.dontCheck hsuper.beam-postgres;
    };
  };

in hpkgs.eigencompanion
