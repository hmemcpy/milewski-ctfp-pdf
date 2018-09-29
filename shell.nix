# nix-shell --pure shell.nix --command 'cd src; make'
let
  rev = "4df3426f5a5e78cef4835897a43abd9e2a092b74";
  sha256 = "05k5mssiqxffxi45mss9wjns6k76i248rpasa48akdcriry1mp63";
  nixpkgs = builtins.fetchTarball {
    inherit sha256;
    url = "https://github.com/NixOS/nixpkgs-channels/archive/${rev}.tar.gz";
  };
in
{ pkgs ? import nixpkgs {} }: with pkgs;

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
        libertine
        mweights
        fontaxes
        mdframed
        needspace
        xifthen
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
        enumitem;
      })
    gnumake
    pythonPackages.pygments
    which
  ];
}
