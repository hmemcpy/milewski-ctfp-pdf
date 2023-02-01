# Category Theory for Programmers

![image](https://user-images.githubusercontent.com/601206/43392303-f770d7be-93fb-11e8-8db8-b7e915b435ba.png)
<b>Direct link:
[category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/download/v1.3.0/category-theory-for-programmers.pdf)</b>
(Latest release: v1.3.0, August 2019. See
[releases](https://github.com/hmemcpy/milewski-ctfp-pdf/releases) for additional
formats and languages.)

[![Build Status](https://travis-ci.org/hmemcpy/milewski-ctfp-pdf.svg?branch=master)](https://travis-ci.org/hmemcpy/milewski-ctfp-pdf)
[(latest CI build)](https://s3.amazonaws.com/milewski-ctfp-pdf/category-theory-for-programmers.pdf)

<img src="https://user-images.githubusercontent.com/601206/47271389-8eea0900-d581-11e8-8e81-5b932e336336.png"
 alt="Buy Category Theory for Programmers" width=410 />
**[Available in full-color hardcover print](https://www.blurb.com/b/9621951-category-theory-for-programmers-new-edition-hardco)**
Publish date: 12 August, 2019. Based off release tag
[v1.3.0](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/tag/v1.3.0). See
[errata-1.3.0](errata-1.3.0.md) for changes and fixes since print.

**[Scala Edition is now available in paperback](https://www.blurb.com/b/9603882-category-theory-for-programmers-scala-edition-pape)**
Publish date: 12 August, 2019. Based off release tag
[v1.3.0](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/tag/v1.3.0). See
[errata-scala](errata-scala.md) for changes and fixes since print.

This is an _unofficial_ PDF version of "Category Theory for Programmers" by
Bartosz Milewski, converted from his
[blogpost series](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
(with permission!)

---

## Building

The best way to build the book is using the [Nix](https://nixos.org/nix/)
package manager. After [installing Nix](https://nixos.org/download.html), if
you're using a non-NixOS operating system, you need to install `nixFlakes` in
your environment following the steps below
([source](https://nixos.wiki/wiki/Flakes#Non-NixOS)):

```bash
$ nix-env -iA nixpkgs.nixFlakes
```

Edit either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and add:

```
experimental-features = nix-command flakes
```

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden
behind feature-flags.

Also, if the Nix installation is in multi-user mode, don’t forget to restart the
nix-daemon.

Afterwards, type `nix flake show` in the root directory of the project to see
all the available versions of this book. Then type `nix build .#<edition>` to
build the edition you want (Haskell, Scala, OCaml, Reason and their printed
versions). For example, to build the Scala edition you'll have to type
`nix build .#ctfp-scala`.

Upon successful compilation, the PDF file will be placed in the `result`
directory inside the root directory `milewski-ctfp-pdf` of the repository.

The file `preamble.tex` contains all the configuration and style declarations.

## Acknowledgements

PDF LaTeX source and the tools to create it are based on the work by Andres Raba
et al., available here: https://github.com/sarabander/sicp-pdf. The book content
is taken, with permission, from Bartosz Milewski's blogpost series, and adapted
to the LaTeX format.

Thanks to the following people for contributing corrections/conversions and
misc:

- Oleg Rakitskiy
- Jared Weakly
- Paolo G. Giarrusso
- Adi Shavit
- Mico Loretan
- Marcello Seri
- Erwin Maruli Tua Pakpahan
- Markus Hauck
- Yevheniy Zelenskyy
- Ross Kirsling
- ...and many others!

The original blog post acknowledgments by Bartosz are consolidated in the
_Acknowledgments_ page at the end of the book.

**Note from Bartosz**: I really appreciate all your contributions. You made this
book much better than I could have imagined. Thank you!

## License

The PDF book, `.tex` files, and associated images and figures in directories
`src/fig` and `src/content` are licensed under Creative Commons
Attribution-ShareAlike 4.0 International License
([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).

The script files `scraper.py` and others are licensed under GNU General Public
License version 3 (for details, see
[LICENSE](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/LICENSE)).
