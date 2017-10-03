Category Theory for Programmers
====

<img src="https://user-images.githubusercontent.com/601206/31094980-ba6af4a4-a7bf-11e7-8857-870346890b44.png"
 alt="Category Theory for Programmers" width=256 align="right" />

<b>Direct link: [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/download/v0.1/category-theory-for-programmers.pdf)</b>  
(Latest release: v0.1, September 2017)

This is an *unofficial* PDF version of "Category Theory for Programmers" by Bartosz Milewski, converted from his [blogpost series](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/).

---

Conversion is done by scraping the blog with [Mercury Web Parser](https://mercury.postlight.com/web-parser/) to get a clean HTML content, modifying and tweaking with [Beautiful Soup](https://www.crummy.com/software/BeautifulSoup/), finally, converting to LaTeX with [Pandoc](https://pandoc.org/). See [scraper.py](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/src/scraper.py) for additional information.

Please [report](https://github.com/hmemcpy/milewski-ctfp-pdf/issues) any formatting/content issues, or better yet, send a PR!

Building
--------

*For macOS Users:* The Inconsolata LGC and Linux Libertine fonts are not included in MacTex. You need to install them separately. Download the Inconsolata LGC fonts [here](https://github.com/MihailJP/Inconsolata-LGC/downloads) and the Linux Libertine fonts [here](http://sourceforge.net/projects/linuxlibertine/files/linuxlibertine/5.3.0/LinLibertineOTF_5.3.0_2012_07_02.tgz/download). To install the fonts system-wide, move all the downloaded `.otf` files into the `/Library/Fonts` folder. After completing these tasks, continue with the instructions below.

The `src` directory contains the LaTeX sources. To recompile the book, go there and enter:

```bash
$ make
```

The file `preamble.tex` contains all the configuration and style declarations.

Chances for successful compilation are increased if you have almost complete installation of recent [TeX Live](https://www.tug.org/texlive/) distribution (the PDF here is compiled with 2017 release). The needed OpenType fonts must be installed in the operating system. You also need [Inkscape](https://inkscape.org/en/download/mac-os/) to recreate image PDFs from SVGs.

To remove all the generated PDFs and auxiliary files in the whole `src` tree:

```bash
$ make clean-all
```

**Tip**: you can use a utility like [entr](http://entrproject.org/) to run a command after any `*.tex` file changes, e.g.:

```bash
$ ls **/*.tex | entr make
```

This will monitor all the `*.tex` files for changes, and will execute the `make` command if any of them changes. This speeds up development significantly, as you can freely modify any of the files, and get almost instant feedback!

Acknowledgements
----------------

PDF LaTeX source and the tools to create it are based on the work by Andres Raba et al., available here: https://github.com/sarabander/sicp-pdf.  
The book content is taken, with permission, from Bartosz Milewski's blogpost series, and adapted to the LaTeX format.

Thanks to the following people for contributing corrections/conversions:

* Oleg Rakitskiy

License
-------

The PDF book, `.tex` files, and associated images and figures in directories `src/fig` and `src/content` are licensed under Creative Commons Attribution-ShareAlike 4.0 International License ([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).

The script files `scraper.py` and others are licensed under GNU General Public License version 3 (for details, see [src/LICENSE](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/src/LICENSE)).
