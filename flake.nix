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

    pythonEnv = python.withPackages (p: [ p.pygments pygments-style-github ]);

    commonAttrs = {
      nativeBuildInputs = [ texliveEnv pythonEnv pkgs.which ];
      FONTCONFIG_FILE = pkgs.makeFontsConf {
        fontDirectories = with pkgs; [ inconsolata-lgc libertine libertinus ];
      };
    };

    mkLatex = variant: edition: let
      maybeVariant = lib.optionalString (variant != null) "-${variant}";
      maybeEdition = lib.optionalString (edition != null) "-${edition}";
      variantStr = if variant == null then "reader" else variant;
      suffix = maybeVariant + maybeEdition;
      basename = "ctfp-${variantStr}${maybeEdition}";
      version = self.shortRev or self.lastModifiedDate;
    in pkgs.stdenv.mkDerivation (commonAttrs // {
      name = "ctfp${suffix}-${version}";
      inherit basename version;
      fullname = "category-theory-for-programmers${suffix}";
      src = "${self}/src";

      configurePhase = ''
        echo -n "\\newcommand{\\OPTversion}{$version}" > version.tex
      '';

      buildPhase = ''
        latexmk -shell-escape -interaction=nonstopmode -halt-on-error \
          -norc -jobname=ctfp -pdflatex="xelatex %O %S" -pdf "$basename.tex"
      '';

      installPhase = "install -m 0644 -vD ctfp.pdf \"$out/$fullname.pdf\"";

      passthru.packageName = "ctfp${suffix}";
    });

    editions = [ null "scala" "ocaml" ];
    variants = [ null "print" ];

  in {
    packages = lib.listToAttrs (lib.concatMap (variant: map (edition: rec {
      name = value.packageName;
      value = mkLatex variant edition;
    }) editions) variants);
    defaultPackage = self.packages.${system}.ctfp;
    devShell = pkgs.mkShell (commonAttrs // {
      nativeBuildInputs = commonAttrs.nativeBuildInputs ++ [
        pkgs.git pkgs.gnumake
      ];
    });
  });
}
