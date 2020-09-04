{
  description = "Category Theory for Programmers";

  inputs.nixpkgs.url = "nixpkgs/nixos-20.03";
  inputs.utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system: let
    pkgs = nixpkgs.legacyPackages.${system};
    inherit (nixpkgs) lib;

    ###########################################################################
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

    ###########################################################################
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

    mkPackageName = edition:
      "ctfp${lib.optionalString (edition != null) "-${edition}"}";

    mkPackage = isShell: edition: pkgs.stdenv.mkDerivation {
      name = mkPackageName edition;
      src = if isShell then null else self;

      makeFlags = [
        "-C" "src" "OUTPUT_DIR=$(out)"
        "GIT_VER=${self.rev or self.lastModifiedDate}"
      ];

      buildFlags = lib.optional (edition != null) edition;

      dontInstall = true;

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
    };

    editions = [ null "scala" "ocaml" ];

  in {
    packages = lib.listToAttrs (map (edition: {
      name = mkPackageName edition;
      value = mkPackage false edition;
    }) editions);
    defaultPackage = self.packages.${system}.ctfp;
    devShell = mkPackage true null;
  });
}
