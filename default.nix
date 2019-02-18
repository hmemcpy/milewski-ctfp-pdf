# nix-shell --pure --command 'cd src; make'
let
  nixpkgs = import <nixpkgs> {};
in
  nixpkgs.callPackage ./shell.nix {}
