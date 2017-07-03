SICP
====

<img src="http://sicpebook.files.wordpress.com/2013/09/dreamsmile3.png"
 alt="Par dreaming and smiling" align="right" />

<b>Direct link: [sicp.pdf](https://github.com/sarabander/sicp-pdf/raw/master/sicp.pdf)</b>

This is a PDF version of "Structure and Interpretation of Computer Programs" by Harold Abelson, Gerald Jay Sussman, and Julie Sussman. It is a further development of the [Unofficial Texinfo Format](http://www.neilvandyke.org/sicp-texi/) (UTF), which was originally derived from the [HTML version](http://mitpress.mit.edu/sicp/) at The MIT Press.

Biggest change in this revision (2.andresraba5) is the conversion to LaTeX, which opens the door to design and customization possibilities that the massive CTAN archive enables. Also, the latest typesetting engine XeTeX can be used, along with the Unicode and OpenType goodness it brings.


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
