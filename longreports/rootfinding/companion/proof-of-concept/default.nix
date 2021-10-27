{ pkgs ? import <nixpkgs> {}
, ghcVersion ? "ghc8107" }:  # ghc8107 matches Danaswap's flake.nix
let
  haskellPackages' = pkgs.haskell.packages.${ghcVersion} // {
    dev = pkgs.haskell.packages.${ghcVersion}.callCabal2nix "eigencompanion-PoC" ./. {};
  };
in {
  eigencompanion = haskellPackages';
}
