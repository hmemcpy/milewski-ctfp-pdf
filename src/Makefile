# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

DIR := $(shell pwd)

all: ctfp.pdf

ctfp.pdf: ctfp.tex
	latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdf -dvi- -ps- $<; \
	mkdir ../out && mv ctfp.pdf ../out/category-theory-for-programmers.pdf

clean:
	latexmk -CA

clean-all: clean
	${RM} ctfp.fls ../out/category-theory-for-programmers.pdf
	rm -rf _minted-ctfp

.PHONY: all clean clean-all
