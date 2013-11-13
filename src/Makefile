# Contributed by holomorph

FIG := $(patsubst %.svg,%.pdf,$(wildcard fig/*/*.svg))

all: sicp.pdf

sicp.pdf: sicp.tex coverpage.pdf ${FIG}
	latexmk -pdflatex="xelatex %O %S" -pdf -dvi- -ps- $<

sicp.tex: sicp.texi
	./texi-to-latex.pl $<

coverpage.pdf: coverpage.svg
	inkscape -f $< -C -A $@

%.pdf: %.svg
	inkscape -f $< -D -A $@

clean:
	latexmk -CA

clean-all: clean
	${RM} ${FIG}

.PHONY: all clean clean-all
