{
  description = "Category Theory for Programmers";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = inputs @ {
    self,
    flake-parts,
    nixpkgs,
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "x86_64-linux"
        "x86_64-darwin"
        "aarch64-linux"
        "aarch64-darwin"
      ];

      perSystem = {
        config,
        pkgs,
        system,
        ...
      }: let
        inherit (nixpkgs) lib;

        pkgs = nixpkgs.legacyPackages.${system};

        ###########################################################################
        # LaTeX Environment
        texliveEnv = pkgs.texlive.combine {
          inherit
            (pkgs.texlive)
            adjustbox
            babel
            bookcover
            catchfile
            chngcntr
            collectbox
            currfile
            emptypage
            enumitem
            environ
            fgruler
            fontaxes
            framed
            fvextra
            idxlayout
            ifmtarg
            ifnextok
            ifplatform
            imakeidx
            import
            l3packages
            lettrine
            libertine
            listings
            mdframed
            microtype
            minifp
            minted
            mweights
            needspace
            newtx
            noindentafter
            nowidow
            scheme-medium
            subfigure
            subfiles
            textpos
            tcolorbox
            tikz-cd
            titlecaps
            titlesec
            todonotes
            trimspaces
            upquote
            wrapfig
            xifthen
            xpatch
            xstring
            zref
            ;
        };

        ###########################################################################
        # Python Environment

        # Pin the Python version and its associated package set in a single place.
        python = pkgs.python310;
        pythonPkgs = pkgs.python310Packages;

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
          propagatedBuildInputs = with pythonPkgs; [pygments];
        };

        pythonEnv = python.withPackages (p: [p.pygments pygments-style-github]);

        commonAttrs = {
          nativeBuildInputs = [texliveEnv pythonEnv pkgs.which];
          FONTCONFIG_FILE = pkgs.makeFontsConf {
            fontDirectories = with pkgs; [inconsolata-lgc libertine libertinus];
          };
        };

        mkLatex = variant: edition: let
          maybeVariant = lib.optionalString (variant != null) "-${variant}";
          maybeEdition = lib.optionalString (edition != null) "-${edition}";
          variantStr =
            if variant == null
            then "reader"
            else variant;
          suffix = maybeVariant + maybeEdition;
          basename = "ctfp-${variantStr}${maybeEdition}";
          version = self.shortRev or self.lastModifiedDate;
        in
          pkgs.stdenv.mkDerivation (commonAttrs
            // {
              inherit basename version;

              name = "ctfp${suffix}-${version}";
              fullname = "ctfp${suffix}";
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

        editions = [null "scala" "ocaml" "reason"];
        variants = [null "print"];
      in rec {
        formatter = pkgs.alejandra;

        packages =
          lib.listToAttrs (lib.concatMap (variant:
            map (edition: rec {
              name = value.packageName;
              value = mkLatex variant edition;
            })
            editions)
          variants)
          // {
            default = self.packages.${system}.ctfp;
          };

        # nix develop .
        devShells.default = pkgs.mkShellNoCC (commonAttrs
          // {
            nativeBuildInputs =
              commonAttrs.nativeBuildInputs
              ++ [
                pkgs.git
                pkgs.gnumake
              ];
          });
      };
    };
}
