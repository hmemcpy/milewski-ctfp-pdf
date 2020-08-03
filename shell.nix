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
in

pkgs.mkShell {
  FONTCONFIG_FILE = pkgs.makeFontsConf { 
    fontDirectories = with pkgs; [ inconsolata-lgc libertine libertinus]; 
  };

  buildInputs = with pkgs; [
    # Misc. build tooling. 
    gnumake
    git
    python3Packages.virtualenv
    which
    # LaTeX Environment.
    texliveEnv
  ];

  shellHook = ''
    # set SOURCE_DATE_EPOCH so that we can use python wheels
    SOURCE_DATE_EPOCH=$(date +%s)
    virtualenv venv
    venv/bin/pip install -v pygments
    venv/bin/pip install -v pygments-style-github
    source venv/bin/activate
  '';
}
