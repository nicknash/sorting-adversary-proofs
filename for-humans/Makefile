.PHONY: all clean checks submission

all: output/pdf/paper.pdf

output/pdf/paper.pdf: paper.tex $(wildcard sections/*.tex)
	mkdir -p build output/pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper.tex
	cp build/paper.pdf $@

checks:
	python3 anc/check_local_volume.py --output anc/check_local_volume.json

submission: output/pdf/paper.pdf
	python3 package_submission.py

clean:
	rm -rf build
