SICP
====

<img src="http://sicpebook.files.wordpress.com/2013/09/dreamsmile3.png"
 alt="Par dreaming and smiling" align="right" />

This is a PDF version of "Structure and Interpretation of Computer Programs" by Harold Abelson, Gerald Jay Sussman, and Julie Sussman. It is a further development of the [Unofficial Texinfo Format](http://www.neilvandyke.org/sicp-texi/) (UTF), which was originally derived from the [HTML version](http://mitpress.mit.edu/sicp/) at The MIT Press.

Biggest change in this revision (2.andresraba5) is the conversion to LaTeX, which opens the door to design and customization possibilities that the massive CTAN archive enables. Also, the latest typesetting engine XeTeX can be used, along with the Unicode and OpenType goodness it brings.


Source
------

The `src` directory contains both Texinfo and LaTeX sources. To recompile the book, enter:

```bash
$ ./texi-to-latex.pl sicp.texi ; xelatex sicp.tex
```

You may need to issue the `xelatex sicp.tex` command again once or twice to get the labels and cross-references right.

The Perl script pulls in both `preamble.tex` and `postamble.tex.` The preamble contains all the configuration and style declarations. Note that the LaTeX file `sicp.tex` will be generated on the fly, overwriting the previous version. To keep `sicp.texi` and `sicp.tex` in sync, I make changes to `sicp.texi,` which is already a hybrid of Texinfo and LaTeX code. This is fine, because all non-Texinfo content remains unchanged by the script.

Chances for successful compilation by `xelatex` are increased if you have almost complete installation of recent TeX Live distribution (the pdf here is compiled with 2012 edition). The needed OpenType fonts must be installed in the operating system.

If compilation stops with "LaTeX Error: Too many unprocessed floats.", you could try to increase the width and height of text area in [preamble](https://github.com/sarabander/sicp-pdf/blob/master/src/preamble.tex#L70-L71). Newer TeX Live or fonts could result in different character metrics, so that some figures no longer fit. The problem is reported in issue [#5](https://github.com/sarabander/sicp-pdf/issues/5).

Acknowledgements
----------------

* Lytha Ayth
* Neil Van Dyke
* Gavrie Philipson
* J. E. Johnson
* Mingshen Sun

License
-------

The files `sicp.texi, sicp.tex, sicp.pdf,` and the diagrams in directory `src/fig` are licensed under Creative Commons Attribution-ShareAlike 3.0 Unported License ([cc by-sa](http://creativecommons.org/licenses/by-sa/3.0/)).
          
The script files `ex-fig-ref.pl, survey.rb,` and `texi-to-latex.pl` are licensed under GNU General Public License version 3 (for details, see src/LICENSE).
