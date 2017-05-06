PAPER=paper.tex

TEX=latex

############################################################

.SUFFIXES: .tex .dvi .ps .pdf

all: paper.pdf

.tex.pdf: paper.bib
	pdf$(TEX) $<
	pdf$(TEX) $<
	bibtex paper
	pdf$(TEX) $<

clean:
	rm -f *~ *.log *.aux *.blg *.bbl
	rm -f paper.pdf

.PHONY: clean

