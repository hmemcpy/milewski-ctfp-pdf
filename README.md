Category Theory for Programmers
====

**Note**: this is a work in progress!

<b>Direct link: [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/raw/master/ctfp.pdf)</b>

This is an *unofficial* PDF version of "Category Theory for Programmers" by Bartosz Milewski, converted from his [blogpost series](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/). 

PDF source and the tools to create it are based on the work by Andres Raba et al., available here: https://github.com/sarabander/sicp-pdf.

Source
------

*For macOS Users:* The Inconsolata LGC and Linux Libertine fonts are not included in MacTex. You need to install them separately. Download the Inconsolata LGC fonts [here](https://github.com/MihailJP/Inconsolata-LGC/downloads) and the Linux Libertine fonts [here](http://sourceforge.net/projects/linuxlibertine/files/linuxlibertine/5.3.0/LinLibertineOTF_5.3.0_2012_07_02.tgz/download). To install the fonts system-wide, move all the downloaded `.otf` files into the `/Library/Fonts` folder. After completing these tasks, continue with the instructions below.

The `src` directory contains both Texinfo and LaTeX sources. To recompile the book, go there and enter:

```bash
$ make
```

The file `preamble.tex` contains all the configuration and style declarations. Note that the LaTeX file `sicp.tex` will be generated on the fly, overwriting the previous version. To keep `sicp.texi` and `sicp.tex` in sync, I make changes to `sicp.texi,` which is already a hybrid of Texinfo and LaTeX code. This is fine, because all non-Texinfo content remains unchanged by the script.

Chances for successful compilation are increased if you have almost complete installation of recent TeX Live distribution (the pdf here is compiled with 2012 release). The needed OpenType fonts must be installed in the operating system. You also need Inkscape to recreate image PDFs from SVGs.

If compilation stops with "LaTeX Error: Too many unprocessed floats.", you could try to increase the width and height of text area in [preamble](https://github.com/sarabander/sicp-pdf/blob/master/src/preamble.tex#L70-L71). Newer TeX Live or updated fonts could result in different character metrics, so that some figures no longer fit. The problem is reported in issue [#5](https://github.com/sarabander/sicp-pdf/issues/5).

To clean up after the build:

```bash
$ make clean
```

This deletes the temporary files written during sicp.pdf creation, including sicp.pdf itself. Move it up to root directory if you want to keep it.

To remove all the generated PDFs and auxiliary files in the whole `src` tree:

```bash
$ make clean-all
```

Acknowledgements
----------------

* Lytha Ayth
* Neil Van Dyke
* Gavrie Philipson
* J. E. Johnson
* Mingshen Sun
* holomorph
* Narumi Katoh
* tfgit
* Brian Wignall
* dine2014

License
-------

The files `sicp.texi, sicp.pdf,` and diagrams in directory `src/fig` are licensed under Creative Commons Attribution-ShareAlike 4.0 International License ([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).
          
The script files `ex-fig-ref.pl, survey.rb,` and `texi-to-latex.pl` are licensed under GNU General Public License version 3 (for details, see src/LICENSE).

Sister project
--------------

A new [HTML5 version](https://github.com/sarabander/sicp) is out, bringing the advantages of adjustable font size and reflowable text to mobile reading.

Translation
-----------

There is a new [Japanese translation](https://github.com/minghai/sicp-pdf/) of the PDF by Narumi Katoh. Great to see new languages joining the collection!
