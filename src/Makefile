# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

FIG := $(patsubst %.svg,%.pdf,$(wildcard fig/*/*.svg))
DIR := $(shell pwd)

all: sicp.pdf

sicp.pdf: sicp.tex exercises.tex figures.tex coverpage.pdf ${FIG}
	latexmk -shell-escape -pdflatex="xelatex %O %S" -pdf -dvi- -ps- $<; \
	mv sicp.pdf ../ctfp.pdf

sicp.tex: sicp.texi preamble.tex postamble.tex texi-to-latex.pl
	./texi-to-latex.pl $<

exercises.tex figures.tex: ex-fig-ref.pl
	./ex-fig-ref.pl -e > exercises.tex; \
	./ex-fig-ref.pl -f > figures.tex

%.pdf: %.svg
	inkscape -f ${DIR}/$< -C -A ${DIR}/$@

clean:
	latexmk -CA

clean-all: clean
	${RM} ${FIG} sicp.tex exercises.tex figures.tex coverpage.pdf sicp.fls

.PHONY: all clean clean-all
