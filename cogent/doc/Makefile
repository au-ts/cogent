.PHONY: all

all: pdf

pdf: doc.tex
	 latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make doc.tex

clean:
	latexmk -CA
	rm -f *.aux *.blg *.out *.bbl *.log
