Category Theory for Programmers (LEAN version)
====

![image](https://user-images.githubusercontent.com/601206/43392303-f770d7be-93fb-11e8-8db8-b7e915b435ba.png)

This is a WORK-IN-PROGRESS attempt to provide a version of the book <b>Direct link: [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/download/v1.3.0/category-theory-for-programmers.pdf)</b> with LEAN [Lean](https://leanprover.github.io/about/) code.  Lean is a theorem prover and functional programming language.
 
This is a fork of the ["unofficial" PDF version](https://github.com/hmemcpy/milewski-ctfp-pdf) of the book.

---

Progress
--------
* Working on Chapter 1


Building
--------

The best way to build the book is using the [Nix](https://nixos.org/nix/) package manager. After [installing Nix](https://nixos.org/download.html), if you're using a non-NixOS operating system, you need to install `nixFlakes` in your environment following the steps below ([source](https://nixos.wiki/wiki/Flakes#Non-NixOS)):

```bash
$ nix-env -iA nixpkgs.nixFlakes
```

Edit either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and add:

```
experimental-features = nix-command flakes
```

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden behind feature-flags.

Also, if the Nix installation is in multi-user mode, don’t forget to restart the nix-daemon. 

Afterwards, type `nix flake show` in the root directory of the project to see all the available versions of this book. Then type `nix build .#<edition>` to build the edition you want (Haskell, Scala, OCaml, Reason and their printed versions). For example, to build the Scala edition you'll have to type `nix build .#ctfp-scala`.

Upon successful compilation, the PDF file will be placed in the `result` directory inside the root directory `milewski-ctfp-pdf` of the repository. 

The file `preamble.tex` contains all the configuration and style declarations.

Acknowledgements
----------------

Please see [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/download/v1.3.0/category-theory-for-programmers.pdf) for the original source and contributors.
License
-------

The PDF book, `.tex` files, and associated images and figures in directories `src/fig` and `src/content` are licensed under Creative Commons Attribution-ShareAlike 4.0 International License ([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).

The script files `scraper.py` and others are licensed under GNU General Public License version 3 (for details, see [LICENSE](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/LICENSE)).
