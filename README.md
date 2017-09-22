Category Theory for Programmers
====

<img src="https://github.com/hmemcpy/milewski-ctfp-pdf/raw/master/src/commutative_diagram.png"
 alt="Category Theory for Programmers" width=256 align="right" />

**Note**: this is a work in progress! Please [report](https://github.com/hmemcpy/milewski-ctfp-pdf/issues) any formatting/content issues!

<b>Direct link: [category-theory-for-programmers.pdf](https://github.com/hmemcpy/milewski-ctfp-pdf/raw/master/ctfp.pdf)</b>

This is an *unofficial* PDF version of "Category Theory for Programmers" by Bartosz Milewski, converted from his [blogpost series](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/).

Conversion is done by scraping the blog with [Mercury Web Parser](https://mercury.postlight.com/web-parser/) to get a clean HTML content, modifying and tweaking with [Beautiful Soup](https://www.crummy.com/software/BeautifulSoup/), finally, converting to LaTeX with [Pandoc](https://pandoc.org/).

See <b>[scraper.py](https://github.com/hmemcpy/milewski-ctfp-pdf/blob/master/src/scraper.py)</b> for additional information.

Acknowledgements
----------------

PDF source and the tools to create it are based on the work by Andres Raba et al., available here: https://github.com/sarabander/sicp-pdf.  
The book content is taken, with permission, from Bartosz Milewski's blogpost series, and adapted to the Texinfo/LaTeX format.

Thanks to the following people for contributing corrections/conversions:

* Oleg Rakitskiy

License
-------

The PDF book, `.tex`/`.texi` files, and associated images and figures in directories `src/fig` and `src/content` are licensed under Creative Commons Attribution-ShareAlike 4.0 International License ([cc by-sa](http://creativecommons.org/licenses/by-sa/4.0/)).

The script files `scraper.py, ex-fig-ref.pl, survey.rb,` and `texi-to-latex.pl` are licensed under GNU General Public License version 3 (for details, see src/LICENSE).
