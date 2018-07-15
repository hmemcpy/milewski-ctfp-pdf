# nix-shell --pure shell.nix --command 'cd src; make'
{ pkgs ? import <nixpkgs> {} }: with pkgs;

mkShell {
  FONTCONFIG_FILE = makeFontsConf { fontDirectories = [ inconsolata-lgc libertine libertinus ]; };
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

        scheme-medium
        listings
        minted
        microtype
        babel
        todonotes
        chngcntr
        ifplatform
        xstring
        enumitem;
      })
    gnumake
    pythonPackages.pygments
    which
  ];
}
