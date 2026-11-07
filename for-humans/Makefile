.PHONY: all clean

all: output/pdf/paper.pdf

output/pdf/paper.pdf: paper.tex references.bib $(wildcard sections/*.tex)
	mkdir -p build output/pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper.tex
	cp build/paper.pdf $@

clean:
	rm -rf build
