PAPER=article.tex

TEX=latex

############################################################

.SUFFIXES: .tex .dvi .ps .pdf

all: article.pdf

.tex.pdf: #article.bib
	pdf$(TEX) $<
	#pdf$(TEX) $<
	#bibtex article
	#pdf$(TEX) $<

clean:
	rm -f *~ *.log *.aux
	rm -f article.pdf

.PHONY: clean

