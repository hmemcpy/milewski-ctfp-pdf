# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

.PHONY: default all clean version.tex

DIR := $(shell pwd)
GIT_VER := $(shell git describe --tags --always --long | tr -d '\n')

# Default top-level LaTeX to generate
DEFAULTTOPTEX = ctfp-reader.tex ctfp-print.tex

SCALATEXFILES = ctfp-reader-scala.tex ctfp-print-scala.tex # todo make this a macro

KOTLINTEXFILES = ctfp-reader-kotlin.tex ctfp-print-kotlin.tex # todo make this a macro

# Top-level LaTeX files from which CTFP book can be generated
TOPTEXFILES = version.tex $(DEFAULTTOPTEX) $(SCALATEXFILES) $(KOTLINTEXFILES)

# Default PDF file to make
DEFAULTPDF:=$(DEFAULTTOPTEX:.tex=.pdf)

# Scala PDF file to make
SCALAPDF:=$(SCALATEXFILES:.tex=.pdf)

# Kotlin PDF file to make
KOTLINPDF:=$(KOTLINTEXFILES:.tex=.pdf)

# Other PDF files for the CTFP book 
TOPPDFFILES:=$(TOPTEXFILES:.tex=.pdf)

# Configuration files
OPTFILES = opt-print-ustrade.tex \
			opt-reader-10in.tex \
			opt-scala.tex \
			opt-kotlin.tex

# All the LaTeX files for the CTFP book in order of dependency
TEXFILES = $(TOPTEXFILES) $(SCALATEXFILES) $(KOTLINTEXFILES) $(OPTFILES)

default: $(DEFAULTPDF) copy # todo cover

scala: version.tex $(SCALAPDF) copy-scala

kotlin: version.tex $(KOTLINPDF) copy-kotlin

# Main targets
$(TOPPDFFILES) : %.pdf : %.tex $(TEXFILES)
	if which latexmk > /dev/null 2>&1 ;\
	then latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdf $< ;\
	else @printf "Error: unable to find latexmk. Is it installed?\n" ;\
	fi

version.tex:
	printf '\\newcommand{\\OPTversion}{' > version.tex
	git describe --tags --always --long | tr -d '\n' >> version.tex
	printf '}' >> version.tex

copy: suffix = ''
copy: copy-task

copy-scala: suffix = '-scala'
copy-scala: copy-task

copy-kotlin: suffix = '-kotlin'
copy-kotlin: copy-task

copy-task:
	@printf 'Creating output directory: $(GIT_VER)\n'
	mkdir -p ../out/$(GIT_VER)
	mv ctfp-reader$(suffix).pdf ../out/$(GIT_VER)/category-theory-for-programmers$(suffix).pdf
	mv ctfp-print$(suffix).pdf ../out/$(GIT_VER)/category-theory-for-programmers$(suffix)-print.pdf

clean:
	rm -f *~ *.aux {ctfp-*}.{out,log,pdf,dvi,fls,fdb_latexmk,aux,brf,bbl,idx,ilg,ind,toc,sed}
	if which latexmk > /dev/null 2>&1 ; then latexmk -CA; fi
	rm -rf ../out

clean-minted:
	rm -rf _minted-*
