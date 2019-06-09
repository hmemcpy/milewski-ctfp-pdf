{ pkgs ? import <nixpkgs> {} }: with pkgs;

mkShell {
  FONTCONFIG_FILE = makeFontsConf { fontDirectories = [ inconsolata-lgc libertine libertinus noto-fonts-cjk ]; };
  buildInputs = [
    (texlive.combine {
        inherit (texlive)
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
        kotex-oblivoir
        kotex-plain
        kotex-utf
        kotex-utils
        unfonts-core
        l3packages;
      })
    gnumake
    pythonPackages.pygments
    which
  ];
}
