# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

FIG := $(patsubst %.svg,%.pdf,$(wildcard fig/*/*.svg))
DIR := $(shell pwd)

all: ctfp.pdf

ctfp.pdf: ctfp.tex coverpage.pdf ${FIG}
	latexmk -shell-escape -pdflatex="xelatex %O %S" -pdf -dvi- -ps- $<; \
	mv ctfp.pdf ../category-theory-for-programmers.pdf

%.pdf: %.svg
	inkscape -f ${DIR}/$< -C -A ${DIR}/$@

clean:
	latexmk -CA

clean-all: clean
	${RM} ${FIG} coverpage.pdf ctfp.fls

.PHONY: all clean clean-all
