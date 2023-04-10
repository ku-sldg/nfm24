BASE_NAME = samplepaper
TEX_SRCS := $(wildcard *.tex)
LATEX = pdflatex
BIBTEX = bibtex

%.pdf:	%.tex
	$(LATEX) $*
	$(BIBTEX) $*
	$(LATEX) $*
	$(LATEX) $*

all:	$(TEX_SRCS:.tex=.pdf)

clean:
	-rm $(TEX_SRCS:.tex=.pdf) $(TEX_SRCS:.tex=.log) $(TEX_SRCS:.tex=.aux)
	-rm $(TEX_SRCS:.tex=.out) $(TEX_SRCS:.tex=.blg) $(TEX_SRCS:.tex=.bbl)
