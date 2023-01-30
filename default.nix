let
  rev = "cecfd08d13ddef8a79f277e67b8084bd9afa1586";
  url = "https://github.com/edolstra/flake-compat/archive/${rev}.tar.gz";
  flake = import (fetchTarball url) {src = ./.;};
  inNixShell = builtins.getEnv "IN_NIX_SHELL" != "";
in
  if inNixShell
  then flake.shellNix
  else flake.defaultNix
