# Igal Tabachnik, 2007.
# Based on work by Andres Raba et al., 2013-2015.

.PHONY: default all clean out-dir version.tex scala ocaml reason

DIR := $(shell pwd)
GIT_VER := $(shell git describe --tags --always --long | tr -d '\n')
OUTPUT_DIR := ../out/$(GIT_VER)

OUTPUT = category-theory-for-programmers

# Default top-level LaTeX to generate
DEFAULTTOPTEX = ctfp-reader.tex ctfp-print.tex

SCALATEXFILES = ctfp-reader-scala.tex ctfp-print-scala.tex # todo make this a macro

OCAMLTEXFILES = ctfp-reader-ocaml.tex ctfp-print-ocaml.tex # todo make this a macro

REASONTEXFILES = ctfp-reader-reason.tex ctfp-print-reason.tex # todo make this a macro

# Top-level LaTeX files from which CTFP book can be generated
TOPTEXFILES = version.tex $(DEFAULTTOPTEX) $(SCALATEXFILES) $(OCAMLTEXFILES) $(REASONTEXFILES)

# Default PDF file to make
DEFAULTPDF:=$(DEFAULTTOPTEX:.tex=.pdf)

# Scala PDF file to make
SCALAPDF:=$(SCALATEXFILES:.tex=.pdf)

# OCaml PDF file to make
OCAMLPDF:=$(OCAMLTEXFILES:.tex=.pdf)

# ReasonML PDF file to make
REASONPDF:=$(REASONTEXFILES:.tex=.pdf)

# Other PDF files for the CTFP book
TOPPDFFILES:=$(TOPTEXFILES:.tex=.pdf)

# Configuration files
OPTFILES = opt-print-ustrade.tex \
			opt-reader-10in.tex \
			opt-scala.tex

# All the LaTeX files for the CTFP book in order of dependency
TEXFILES = $(TOPTEXFILES) $(SCALATEXFILES) $(OCAMLTEXFILES) $(REASONTEXFILES) $(OPTFILES)

default: suffix=''
default: out-dir $(DEFAULTPDF) # todo cover

all: clean default scala ocaml

scala: suffix='-scala'
scala: clean out-dir version.tex $(SCALAPDF)

ocaml: suffix='-ocaml'
ocaml: clean out-dir version.tex $(OCAMLPDF)

reason: suffix='-reason'
reason: clean out-dir version.tex $(REASONPDF)

# Main targets
$(TOPPDFFILES) : %.pdf : %.tex $(TEXFILES)
	if which latexmk > /dev/null 2>&1 ;\
	then \
		latexmk -shell-escape -interaction=nonstopmode -halt-on-error -norc -jobname=ctfp -pdflatex="xelatex %O %S" -pdf $< ;\
		mv ctfp.pdf $(OUTPUT_DIR)/$(subst ctfp,$(OUTPUT),$(subst ctfp-reader,$(OUTPUT),$*)).pdf ;\
	else @printf "Error: unable to find latexmk. Is it installed?\n" ;\
	fi

version.tex:
	@printf '\\newcommand{\\OPTversion}{' > version.tex
	@printf $(GIT_VER) >> version.tex
	@printf '}' >> version.tex

out-dir:
	@printf 'Creating output directory: $(OUTPUT_DIR)\n'
	mkdir -p $(OUTPUT_DIR)

clean:
	rm -f *~ *.aux {ctfp-*}.{out,log,pdf,dvi,fls,fdb_latexmk,aux,brf,bbl,idx,ilg,ind,toc,sed}
	if which latexmk > /dev/null 2>&1 ; then latexmk -CA; fi
	rm -rf ../out

clean-minted:
	rm -rf _minted-*
