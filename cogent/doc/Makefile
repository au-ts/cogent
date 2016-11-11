.PHONY: all

all: pdf newtc

pdf: doc.tex
	 latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make doc.tex

newtc: new-tc.tex
	 latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make new-tc.tex
clean:
	latexmk -CA
	rm -f *.aux *.blg *.out *.bbl *.log
