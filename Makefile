OUTPUT ?= $(shell basename "$(shell dirname "$(INPUT)")")
OUTPUT_DIRECTORY = $(shell pwd)/build
LATEXMK_ARGS ?= -f -file-line-error -shell-escape -logfilewarninglist -interaction=nonstopmode -halt-on-error -norc -pdflatex="xelatex %O %S" -pdfxe
TEXINPUTS = ""
TEXLIVE_RUN = TEXINPUTS=$(TEXINPUTS)
LATEXMK_COMMAND = $(TEXLIVE_RUN) latexmk $(LATEXMK_ARGS)

# Make does not offer a recursive wildcard function, so here's one:
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

ctfp:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp ctfp-reader.tex

ctfp-epub:
	cd src; tex4ebook -l -s -t -c ctfp-reader -f epub+dvisvgm_hashes ctfp-reader.tex || { status=$$?; test -f ctfp-reader.epub && test -f ctfp-reader-epub/ctfp-reader.epub && exit 0; exit $$status; }

ctfp-ocaml:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp-ocaml ctfp-reader-ocaml.tex

ctfp-scala:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp-scala ctfp-reader-scala.tex

ctfp-print:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp-print ctfp-print.tex

ctfp-print-ocaml:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp-print-ocaml ctfp-print-ocaml.tex

ctfp-print-scala:
	cd src; $(LATEXMK_COMMAND) -jobname=ctfp-print-scala ctfp-print-scala.tex

lint:
	$(foreach file, $(call rwildcard,$(shell dirname "$(INPUT)"),*.tex), latexindent -l -w $(file);)
