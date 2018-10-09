Category Theory for Programmers
====


<img src="https://user-images.githubusercontent.com/601206/44096015-e3edb674-9fe2-11e8-8bfb-2b59cf857876.png"
 alt="Category Theory for Programmers" width=256 align="right" />

![image](https://user-images.githubusercontent.com/601206/43392303-f770d7be-93fb-11e8-8db8-b7e915b435ba.png)
<b>Direct link: [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/releases/download/v1.0.0/category-theory-for-programmers.pdf)</b>  
(Latest release: v1.0.0, October 2018)

[![Build Status](https://travis-ci.org/hmemcpy/milewski-ctfp-pdf.svg?branch=master)](https://travis-ci.org/hmemcpy/milewski-ctfp-pdf)  
[(latest CI build)](https://s3.amazonaws.com/milewski-ctfp-pdf/category-theory-for-programmers.pdf)

This is an *unofficial* PDF version of "Category Theory for Programmers" by Bartosz Milewski, converted from his [blogpost series](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/).

---

Conversion is done by scraping the blog with [Mercury Web Parser](https://mercury.postlight.com/web-parser/) to get a clean HTML content, modifying and tweaking with [Beautiful Soup](https://www.crummy.com/software/BeautifulSoup/), finally, converting to LaTeX with [Pandoc](https://pandoc.org/). See [scraper.py](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/src/scraper.py) for additional information.

Please [report](https://github.com/hmemcpy/milewski-ctfp-pdf/issues) any formatting/content issues, or better yet, send a PR!

Building
--------

Chances for successful compilation are increased if you have almost complete installation of recent [TeX Live 2017](https://www.tug.org/texlive/) distribution (the PDF here is compiled with 2017 release). The needed OpenType fonts must be installed in the operating system. In addition, [pygments](http://pygments.org/) for Python must be installed as well.

The `src` directory contains the LaTeX sources. To recompile the book, go there and enter:

```bash
$ make
```

Upon successful compilation, the files will be placed in the `out` directory next to `src`. 

The file `preamble.tex` contains all the configuration and style declarations.

Acknowledgements
----------------

PDF LaTeX source and the tools to create it are based on the work by Andres Raba et al., available here: https://github.com/sarabander/sicp-pdf.  
The book content is taken, with permission, from Bartosz Milewski's blogpost series, and adapted to the LaTeX format.

Thanks to the following people for contributing corrections/conversions and misc:

* Oleg Rakitskiy
* Jared Weakly
* Paolo G. Giarrusso
* Adi Shavit
* Mico Loretan
* Marcello Seri
* Erwin Maruli Tua Pakpahan
* Markus Hauck
* Yevheniy Zelenskyy
* ...and many others!

Note from Bartosz: I really appreciate all your contributions. You made this book much better than I could have imagined. Thank you!

License
-------

The PDF book, `.tex` files, and associated images and figures in directories `src/fig` and `src/content` are licensed under Creative Commons Attribution-ShareAlike 4.0 International License ([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).

The script files `scraper.py` and others are licensed under GNU General Public License version 3 (for details, see [LICENSE](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/LICENSE)).
