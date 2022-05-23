# { nixpkgs ? import <nixpkgs> {} }:
# let
#   sources = {
#     haskellNix = builtins.fetchTarball "https://github.com/input-output-hk/haskell.nix/archive/master.tar.gz";
#   };
#   haskellNix = import sources.haskellNix {};

#   # Import nixpkgs and pass the haskell.nix provided nixpkgsArgs
#   pkgs = import haskellNix.sources.nixpkgs haskellNix.nixpkgsArgs;
# in pkgs.haskell-nix.project {
#   src = pkgs.haskell-nix.haskellLib.cleanGit {
#     name = "tla-transmutation";
#     src = ./.;
#   };

#   compiler-nix-name = "ghc8102";
# }
{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs;
  inherit (pkgs) haskellPackages;

  haskellDeps = ps: with ps; [
    base
    aeson
    casing
    extra
  ];

  ghc = haskellPackages.ghcWithPackages haskellDeps;

  nixPackages = [
    ghc
    nixpkgs.haskellPackages.haskell-language-server
    nixpkgs.haskellPackages.hlint
    nixpkgs.haskellPackages.apply-refact
    nixpkgs.haskellPackages.hoogle
    nixpkgs.haskellPackages.hindent
    nixpkgs.haskellPackages.hasktags
    nixpkgs.haskellPackages.happy
    nixpkgs.haskellPackages.stylish-haskell
  ];
in
pkgs.stdenv.mkDerivation {
  name = "env";
  buildInputs = nixPackages;
}
