# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

.PHONY: default all clean version.tex

DIR := $(shell pwd)

# Default top-level LaTeX to generate
DEFAULTTOPTEX = ctfp-reader.tex

# Top-level LaTeX files from which CTFP book can be generated
TOPTEXFILES = version.tex $(DEFAULTTOPTEX)

# Default PDF file to make
DEFAULTPDF:=$(DEFAULTTOPTEX:.tex=.pdf)
# Other PDF files for the CTFP book 
TOPPDFFILES:=$(TOPTEXFILES:.tex=.pdf)

# Configuration files
OPTFILES = opt-print-ustrade.tex \
           opt-reader-10in.tex

# All the LaTeX files for the CTFP book in order of dependency
TEXFILES = $(TOPTEXFILES) $(OPTFILES)

default: $(DEFAULTPDF)

all: $(TOPPDFFILES) # todo cover

# Main targets
$(TOPPDFFILES) : %.pdf : %.tex $(TEXFILES) 
	if which latexmk > /dev/null 2>&1 ;\
	then latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdf $< ;\
	else echo "Error: unable to find latexmk. Is it installed?" ;\
	fi


# ctfp.pdf: ctfp.tex
# 	latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdf -dvi- -ps- $<; \
# 	mkdir -p ../out && mv ctfp.pdf ../out/category-theory-for-programmers.pdf

version.tex:
	/bin/echo -n '\newcommand{\OPTversion}{' > version.tex
	git describe --always --long | tr -d '\n' >> version.tex
	/bin/echo -n '}' >> version.tex

clean:
	latexmk -CA

clean-all: clean
	${RM} ctfp.fls ../out/category-theory-for-programmers.pdf
	rm -rf _minted-ctfp
