# This commit corresponds to a recent (as of 2 August 2020) pin of the 20.03
# nixpkgs branch.
import (
  builtins.fetchTarball {
    url = "https://github.com/nixos/nixpkgs/archive/7dc4385dc7b5b2c0dbfecd774cebbc87ac05c061.tar.gz";
    sha256 = "10xr87ilxypz8fya6q42vsk5rmavv1bjrxhkznr9fvn514am58xb";
  }
)
