{ pkgs ? import ./pinned.nix {} }:

let
  #############################################################################
  # LaTeX Environment
  texliveEnv = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      bookcover
      textpos
      fgruler
      tcolorbox
      fvextra
      framed
      newtx
      nowidow
      emptypage
      wrapfig
      subfigure
      adjustbox
      collectbox
      tikz-cd
      imakeidx
      idxlayout
      titlesec
      subfiles
      lettrine
      upquote
      libertine
      mweights
      fontaxes
      mdframed
      needspace
      xifthen
      ifnextok
      currfile
      noindentafter
      ifmtarg
      scheme-medium
      listings
      minted
      microtype
      babel
      todonotes
      chngcntr
      ifplatform
      xstring
      minifp
      titlecaps
      enumitem
      environ
      trimspaces
      l3packages
      zref
      catchfile
      import
      ;
  };

  #############################################################################
  # Python Environment

  # Pin the Python version and its associated package set in a single place.
  python = pkgs.python38;
  pythonPkgs = pkgs.python38Packages;

  pygments-style-github = pythonPkgs.buildPythonPackage rec {
    pname = "pygments-style-github";
    version = "0.4";

    doCheck = false; # Hopefully someone else has run the tests.

    src = pythonPkgs.fetchPypi {
      inherit pname version;
      sha256 = "19zl8l5fyb8z3j8pdlm0zbgag669af66f8gn81ichm3x2hivvjhg";
    };

    # Anything depending on this derivation is probably also gonna want
    # pygments to be available.
    propagatedBuildInputs = with pythonPkgs; [ pygments ];
  };

  pythonEnv = python.withPackages (
    pyPkgs: with pyPkgs; [
      pygments
      pygments-style-github
    ]
  );
in

pkgs.mkShell {
  FONTCONFIG_FILE = pkgs.makeFontsConf {
    fontDirectories = with pkgs; [ inconsolata-lgc libertine libertinus ];
  };

  buildInputs = with pkgs; [
    # Misc. build tooling. 
    gnumake
    git
    python3Packages.virtualenv
    which
    # LaTeX Environment (with all associated libraries and packages).
    texliveEnv
    # Python Environment (with all associated libraries and packages).
    pythonEnv
  ];
}
