![GitHub stars][github stars]
[![GitHub Workflow Status][github workflow status]][github actions link]
[![Download][download badge]][github latest release]
[![License][license badge]][github latest release]

# Category Theory For Programmers

An _unofficial_ PDF version of "**C**ategory **T**heory **F**or **P**rogrammers"
by [Bartosz Milewski][bartosz github], converted from his [blogpost
series][blogpost series] (_with permission!_).

![Category Theory for Programmers][ctfp image]

## Buy the book

- **[Standard edition in full-color hardcover
  print][buy regular edition on blurb]**
  - Publish date: 12 August, 2019.
  - Based off release tag [v1.3.0][v1.3.0 github release link]. See
    [errata-1.3.0](errata-1.3.0.md) for changes and fixes since print.
- **[Scala Edition in paperback][buy scala edition on blurb]**
  - Publish date: 12 August, 2019.
  - Based off release tag [v1.3.0][v1.3.0 github release link]. See
    [errata-scala](errata-scala.md) for changes and fixes since print.

## Build the book

The building workflow requires [Nix][nix website]. After [installing
Nix][nix download website], you need to enable the upcoming "flake" feature
which must be [enabled manually][nixos wiki flake] the time being. This is
needed to expose the new Nix commands and flakes support that are hidden behind
feature-flags.

Afterwards, type `nix flake show` in the root directory of the project to see
all the available versions of this book. Then type `nix build .#<edition>` to
build the edition you want (Haskell, Scala, OCaml, Reason and their printed
versions). For example, to build the Scala edition you'll have to type
`nix build .#ctfp-scala`.

Upon successful compilation, the PDF file will be placed in the `result`
directory.

The command `nix develop` will provide a shell containing all the required
dependencies to build the book manually using the provided `Makefile`. To build
the `ctfp-scala` edition, just run `make ctfp-scala`.

## Contribute

Contributors are welcome to contribute to this book by sending pull-requests.
Once reviewed, the changes are merged in the main branch and will be
incorporated in the next release.

**Note from [Bartosz][bartosz github]**: I really appreciate all your
contributions. You made this book much better than I could have imagined. Thank
you!

Find the [list of contributors on Github][contributors].

## Acknowledgements

PDF LaTeX source and the tools to create it are based on the work by [Andres
Raba][andres raba github]. The book content is taken, with permission, from
[Bartosz Milewski][bartosz github]'s blogpost series, and adapted to the LaTeX
format.

The original blog post acknowledgments by Bartosz are consolidated in the
_Acknowledgments_ page at the end of the book.

## License

The PDF book, `.tex` files, and associated images and figures in directories
`src/fig` and `src/content` are licensed under [Creative Commons
Attribution-ShareAlike 4.0 International License][license cc by sa].

The script files `scraper.py` and others are licensed under [GNU General Public
License version 3][license gnu gpl].

[download badge]:
  https://img.shields.io/badge/Download-latest-green.svg?style=flat-square
[github actions link]: https://github.com/hmemcpy/milewski-ctfp-pdf/actions
[github stars]:
  https://img.shields.io/github/stars/hmemcpy/milewski-ctfp-pdf.svg?style=flat-square
[github workflow status]:
  https://img.shields.io/github/actions/workflow/status/hmemcpy/milewski-ctfp-pdf/nix-flake-check.yaml?branch=master&style=flat-square
[github latest release]:
  https://github.com/hmemcpy/milewski-ctfp-pdf/releases/latest
[license badge]:
  https://img.shields.io/badge/License-CC_By_SA-green.svg?style=flat-square
[ctfp image]:
  https://user-images.githubusercontent.com/601206/47271389-8eea0900-d581-11e8-8e81-5b932e336336.png
[bartosz github]: https://github.com/BartoszMilewski
[nixos wiki flake]: https://nixos.wiki/wiki/Flakes
[andres raba github]: https://github.com/sarabander
[contributors]: https://github.com/hmemcpy/milewski-ctfp-pdf/graphs/contributors
[license cc by sa]: https://spdx.org/licenses/CC-BY-SA-4.0.html
[license gnu gpl]: https://spdx.org/licenses/GPL-3.0.html
[blogpost series]:
  https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/
[buy regular edition on blurb]:
  https://www.blurb.com/b/9621951-category-theory-for-programmers-new-edition-hardco
[buy scala edition on blurb]:
  https://www.blurb.com/b/9603882-category-theory-for-programmers-scala-edition-pape
[v1.3.0 github release link]:
  https://github.com/hmemcpy/milewski-ctfp-pdf/releases/tag/v1.3.0
[nix website]: https://nixos.org/nix/
[nix download website]: https://nixos.org/download.html
