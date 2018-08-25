# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

.PHONY: default all clean version.tex

DIR := $(shell pwd)
GIT_VER := $(shell git describe --always --long | tr -d '\n')

# Default top-level LaTeX to generate
DEFAULTTOPTEX = ctfp-reader.tex ctfp-print.tex

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

default: $(DEFAULTPDF) copy

all default: copy# todo cover

# Main targets
$(TOPPDFFILES) : %.pdf : %.tex $(TEXFILES) 
	if which latexmk > /dev/null 2>&1 ;\
	then latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdf $< ;\
	else echo "Error: unable to find latexmk. Is it installed?" ;\
	fi

version.tex:
	/bin/echo -n '\newcommand{\OPTversion}{' > version.tex
	git describe --always --long | tr -d '\n' >> version.tex
	/bin/echo -n '}' >> version.tex

copy:
	echo 'Creating output directory: $(GIT_VER)'
	mkdir -p ../out/$(GIT_VER)
	mv ctfp-reader.pdf ../out/$(GIT_VER)/category-theory-for-programmers.pdf
	mv ctfp-print.pdf ../out/$(GIT_VER)/category-theory-for-programmers-print.pdf

clean:
	rm -f *~ *.aux {ctfp-*}.{out,log,pdf,dvi,fls,fdb_latexmk,aux,brf,bbl,idx,ilg,ind,toc,sed}
	rm -rf _minted-ctfp
	if which latexmk > /dev/null 2>&1 ; then latexmk -CA; fi
	rm -rf ../out